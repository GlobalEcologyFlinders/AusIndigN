#########################################################################
## Estimating size of pre-colonial Indigenous population in Australia  ##
## August 2024                                                         ##
## CJA Bradshaw                                                        ##
#########################################################################

## libraries
library(sp)
library(raster)
library(oceanmap)
library(OceanView)
library(abind)
library(pracma)
library(binford)
library(rgl)
library(scatterplot3d) 
library(spatstat)
library(spatialEco)
library(SpatialPack)
library(performance)
library(sjPlot)
library(dismo)
library(gbm)
library(truncnorm)
library(bootstrap)

## source functions
source("matrixOperators.r")
source("new_lmer_AIC_tables3.R") 
source("r.squared.R") 

## custom functions
# gradient function for immigration
# pI ~ a / (1 + (b * exp(-c * Rk)))
aI <- 0.95; bI <- 5000; cI <- 3
pI.func <- function(Rk) {
  pI <- aI / (1 + (bI * exp(-cI * Rk)))
  return(pI)}
pI.func(4)
xI <- seq(1,10,0.01)
yI <- pI.func(xI)

# gradient function for emigration
aE <- 1; bE <- -3.2
pE.func <- function(Rk) {
  pE <- aE * exp(bE * Rk)
  return(pE)}
pE.func(0.5)
xE <- seq(0.01,1,0.01)
yE <- pE.func(xE)
pE.out <- data.frame(xE,yE)

# stochastic beta sampler (single sample)
stoch.beta.func <- function(mu, var) {
  Sx <- rbeta(length(mu), (((1 - mu) / var - 1 / mu) * mu ^ 2), ((((1 - mu) / var - 1 / mu) * mu ^ 2)*(1 / mu - 1)))
  return(params=Sx)
}

# stochastic beta sampler (n samples)
stoch.n.beta.func <- function(n, mu, var) {
  Sx <- rbeta(n, (((1 - mu) / var - 1 / mu) * mu ^ 2), ((((1 - mu) / var - 1 / mu) * mu ^ 2)*(1 / mu - 1)))
  return(params=Sx)
}

# dynamics model function
Nproj.func <- function(Nt, rm, K) {
  Nt1 <- round(Nt * exp(rm*(1-(Nt/K))), 0)
  return(Nt1)
}

# rescale a range
rscale <- function (x, nx1, nx2, minx, maxx) {
  nx = nx1 + (nx2 - nx1) * (x - minx)/(maxx - minx)
  return(nx)
}

# matrix rotation
rot.mat <- function(x) t(apply(x, 2, rev))

# matrix poisson resampler
rpois.fun <- function(x,y,M) {
  rpois(1,M[x,y])
}
rpois.vec.fun <- Vectorize(rpois.fun,vectorize.args = c('x','y'))

## list coordinates to xyz
coordlist2xyz <- function (list) {
  rl <- length(list[[1]]); cl <- length(list[[2]])
  coords <- c(NA,NA)
  for (r in 1:rl) {
    for (c in 1:cl) {
      coords <- rbind(coords, c(list[[1]][r],list[[2]][c]))
    }
  }
  coords <- coords[-1,]
  return(coordxyz=coords)
}

# AIC corrected for small n
AICc <- function(...) {
  models <- list(...)
  num.mod <- length(models)
  AICcs <- numeric(num.mod)
  ns <- numeric(num.mod)
  ks <- numeric(num.mod)
  AICc.vec <- rep(0,num.mod)
  for (i in 1:num.mod) {
    if (length(models[[i]]$df.residual) == 0) n <- models[[i]]$dims$N else n <- length(models[[i]]$residuals)
    if (length(models[[i]]$df.residual) == 0) k <- sum(models[[i]]$dims$ncol) else k <- (length(models[[i]]$coeff))+1
    AICcs[i] <- (-2*logLik(models[[i]])) + ((2*k*n)/(n-k-1))
    ns[i] <- n
    ks[i] <- k
    AICc.vec[i] <- AICcs[i]
  }
  return(AICc.vec)
}

# information-criteria functions
delta.IC <- function(x) x - min(x) ## where x is a vector of an IC
weight.IC <- function(x) (exp(-0.5*x))/sum(exp(-0.5*x)) ## Where x is a vector of dIC
ch.dev <- function(x) ((( as.numeric(x$null.deviance) - as.numeric(x$deviance) )/ as.numeric(x$null.deviance))*100) ## % change in deviance, where x is glm object

# evidence ratio
linreg.ER <- function(x,y) { # where x and y are vectors of the same length; calls AICc, delta.AIC, weight.AIC functions
  fit.full <- lm(y ~ x); fit.null <- lm(y ~ 1)
  AIC.vec <- c(AICc(fit.full),AICc(fit.null))
  dAIC.vec <- delta.IC(AIC.vec); wAIC.vec <- weight.IC(dAIC.vec)
  ER <- wAIC.vec[1]/wAIC.vec[2]
  r.sq.adj <- as.numeric(summary(fit.full)[9])
  return(c(ER,r.sq.adj))
}

################################
## estimating carrying capacity
################################

## set grids

## NPP (HadCM3)
nppH <- read.table("NppSahul(0-140ka_rawvalues)_Krapp2021.csv", header=T, sep=",") # 0.5 deg lat resolution
not.naH <- which(is.na(nppH[,3:dim(nppH)[2]]) == F, arr.ind=T)
upper.rowH <- as.numeric(not.naH[1,1])
lower.rowH <- as.numeric(not.naH[dim(not.naH)[1],1])
min.latH <- max(nppH[not.naH[,1], 1])  
max.latH <- min(nppH[not.naH[,1], 1])
min.lonH <- min(nppH[not.naH[,1], 2])
max.lonH <- max(nppH[not.naH[,1], 2])

sahul.subH <- rep(0, dim(nppH)[1])
for (n in 1:dim(nppH)[1]) {
  sahul.subH[n] <- ifelse(nppH[n,1] <= min.latH & nppH[n,1] >= max.latH & nppH[n,2] >= min.lonH & nppH[n,2] <= max.lonH, 1, 0)
}  
sah.keepH <- which(sahul.subH == 1)
nppH.sah <- nppH[sah.keepH,]

# Siler hazard h(x) (Gurven et al. 2007)
# average hunter-gatherer
a1 <- 0.422 # initial infant mortality rate (also known as αt)
b1 <- 1.131 # rate of mortality decline (also known as bt)
a2 <- 0.013 # age-independent mortality (exogenous mortality due to environment); also known as ct
a3 <- 1.47e-04 # initial adult mortality rate (also known as βt)
b3 <- 0.086 # rate of mortality increase
longev <- 80
x <- seq(0,longev,1) # age vector
h.x <- a1 * exp(-b1*x) + a2 + a3 * exp(b3 * x) # Siler's hazard model
l.x <- exp((-a1/b1) * (1 - exp(-b1*x))) * exp(-a2 * x) * exp(a3/b3 * (1 - exp(b3 * x))) # Siler's survival (proportion surviving) model

l.inf <- exp(-a1/b1) # survival at infinite time
T.m <- 1/b1 # time constant at which maturity is approached
h.m <- a2 # hazard for mature animals
l.m <- exp(-a2*x) # survival
h.s <- a3*exp(b3*x) # hazard for senescence
l.s <- exp((a3/b3)*(1 - exp(b3*x))) # survival for senescence
f.x <- a3*exp(b3*x)*exp((a3/b3)/(1-exp(b3*x))) # probability density function
(log(a3) - log(a1)) / a3
T.s <- (1/b3) # modal survival time

## survival
init.pop <- 10000
lx <- round(init.pop*l.x,0)
len.lx <- length(lx)
dx <- lx[1:(len.lx-1)]-lx[2:len.lx]
qx <- dx/lx[1:(length(lx)-1)]
Sx <- 1 - qx
sx <- lx[2:len.lx]/lx[1:(len.lx-1)]
mx <- 1 - sx
Lx <- (lx[1:(len.lx-1)] + lx[2:len.lx])/2
ex <- rev(cumsum(rev(Lx)))/lx[-len.lx]
ex.avg <- ex + x[-len.lx]

# set SD for Sx
Sx.sd <- 0.05 # can set to any value

# fertility (Walker et al. 2006)
primiparity.walker <- c(17.7,18.7,19.5,18.5,18.5,18.7,25.7,19,20.5,18.8,17.8,18.6,22.2,17,16.2,18.4)
prim.mean <- round(mean(primiparity.walker),0)
prim.lo <- round(quantile(primiparity.walker,probs=0.025),0)
prim.hi <- round(quantile(primiparity.walker,probs=0.975),0)
dat.world13 <- read.table("world2013lifetable.csv", header=T, sep=",")
fert.world13 <- dat.world13$m.f
fert.trunc <- fert.world13[1:(longev+1)]
pfert.trunc <- fert.trunc/sum(fert.trunc)
fert.bentley <- 4.69/2 # Bentley 1985 for !Kung
fert.vec <- fert.bentley * pfert.trunc

## construct matrix
stages <- len.lx
popmat <- matrix(0,nrow=stages,ncol=stages)
colnames(popmat) <- x
rownames(popmat) <- x

## populate matrix
popmat[1,] <- fert.vec
diag(popmat[2:stages,]) <- Sx
popmat[stages,stages] <- 0 # Sx[stages-1]
popmat.orig <- popmat ## save original matrix

## matrix properties
r.ann <- max.r(popmat) # rate of population change, 1-yr
#stable.stage.dist(popmat) ## stable stage distribution
R.val(popmat,stages) # reproductive value
gen.l <- G.val(popmat,stages) # mean generation length

## for r.max (set Sx=1)
Sx.1 <- Sx
Sx.1[] <- 1
popmat.max <- popmat.orig
diag(popmat.max[2:stages,]) <- Sx.1
popmat.max[stages,stages] <- 0 # Sx[stages-1]
max.lambda(popmat.max) ## 1-yr lambda
rm.ann <- max.r(popmat.max) # rate of population change, 1-yr

#stable.stage.dist(popmat) ## stable stage distribution
R.val(popmat,stages) # reproductive value
gen.l <- G.val(popmat,stages) # mean generation length

### population dynamics parameters
# dynamical model
# Nt+1 = Nt * exp(rm*(1-(Nt/K))) - (E - I)
lambda.ann <- exp(r.ann) # annual lambda
r.max.NEE <- 2 * log(lambda.ann^gen.l) # human rmax at generational scale (arbitrarily double)
lambda.max.ann <- exp(rm.ann)
rm.max.NEE <- log(lambda.max.ann^gen.l) # human rmax at generational scale (from Sx=1 Leslie matrix)

# Cole's allometric calculation (high)
alpha.Ab <- 15
a.Cole <- -0.16
a.lo.Cole <- -0.41
a.up.Cole <- 0.10
a.sd.Cole <- mean(c((a.Cole - a.lo.Cole)/1.96, (a.up.Cole - a.Cole)/1.96))
b.lo.Cole <- -1.2
b.up.Cole <- -0.79
b.Cole <- -0.99
b.sd.Cole <- mean(c((b.Cole - b.lo.Cole)/1.96, (b.up.Cole - b.Cole)/1.96))
r.max.Cole <- 10^(a.Cole + b.Cole*log10(alpha.Ab)) # from Hone et al. 2003-JApplEcol
r.max.lo.Cole <- 10^(a.lo.Cole + b.lo.Cole*log10(alpha.Ab))
r.max.up.Cole <- 10^(a.up.Cole + b.up.Cole*log10(alpha.Ab))

r.max.up.gen.Cole <- log((exp(r.max.up.Cole))^gen.l)
r.max.gen.Cole <- log((exp(r.max.Cole))^gen.l)
r.max.lo.gen.Cole <- log((exp(r.max.lo.Cole))^gen.l)
r.max.gen.Cole.sd <- mean(c((r.max.gen.Cole - r.max.lo.gen.Cole)/1.96, (r.max.up.gen.Cole - r.max.gen.Cole)/1.96))


    ### relationship between NPP and K
    K.NPP <- "rotated parabolic"

    # npp @ modern
    sub.modH <- which(colnames(nppH.sah) == paste("X",0,sep=""))
    nppH.sah.mod <- nppH.sah[,c(1,2,sub.modH)]
    
    # plot raster
    coordinates(nppH.sah.mod) = ~ Lon + Lat
    proj4string(nppH.sah.mod)=CRS("+proj=longlat +datum=WGS84") # set it to lat-long
    gridded(nppH.sah.mod) = TRUE
    nppH.mod = raster(nppH.sah.mod)

    lim.exts <- 5

    lzH <- dim(nppH.sah)[2] - 2
    nppH.array <- array(data=NA, dim=c(dim(raster2matrix(nppH.mod)),lzH))
    for (k in 3:(lzH+2)) {
      nppH.sah.k <- nppH.sah[,c(1,2,k)] 
      coordinates(nppH.sah.k) = ~ Lon + Lat
      proj4string(nppH.sah.k)=CRS("+proj=longlat +datum=WGS84") # set it to lat-long
      gridded(nppH.sah.k) = TRUE
      nppH.k = raster(nppH.sah.k)
      nppH.array[,,k-2] <- raster2matrix(nppH.k)
    }
    image((nppH.array[,,5]), col=rev(grey(1:100/100)))
    
    ## NPP temporal outputs 40 ka—present
    t1000Hvec <- 0:40
    nppH.array.40pres <- nppH.array[,,1:length(t1000Hvec)]
    dim(nppH.array.40pres)
    image((nppH.array.40pres[,,1]), col=rev(grey(1:100/100)))

    AUS.nppH.array.40pres1 <- nppH.array.40pres[, 1:66, ]
    dim(AUS.nppH.array.40pres1)
    AUS.nppH.array.40pres <- AUS.nppH.array.40pres1[-c(88),-c(65:66),]
    dim(AUS.nppH.array.40pres)
    AUS.nppH.array.40pres[87,64,1] <- NA
    AUS.nppH.array.pres <- AUS.nppH.array.40pres[,,1]
    dim(AUS.nppH.array.pres)
    image(AUS.nppH.array.40pres[,,1], col=rev(grey(1:100/100)))

    # Tasmania, not including Bass Strait islands Jones, Blomely, Reynolds, O'Ryan (estimates for pre-contact)
    # 42° 01' 17" South, 146° 35' 36":  42+(01/60)+(17/(60*60)) = -42.02; 146+(35/60)+(36/(60*60)) = 146.5933
    TAS.nppH.array.pres <- AUS.nppH.array.pres[69:77,1:6]
    TAS.nppH.array.40pres <- AUS.nppH.array.40pres[69:77,1:6,]
    image(TAS.nppH.array.pres, col=rev(grey(1:100/100)))
    
    # full area
    ALL.nppH.40pres <- apply(nppH.array.40pres, 3, mean, na.rm=T)
    length(ALL.nppH.40pres)
    plot(t1000Hvec,ALL.nppH.40pres, type="l")

    # AUS
    AUS.nppH.40pres <- apply(AUS.nppH.array.40pres, 3, mean, na.rm=T)
    length(AUS.nppH.40pres)
    plot(t1000Hvec,AUS.nppH.40pres, type="l")
    
    # TAS
    TAS.nppH.40pres <- apply(TAS.nppH.array.40pres, 3, mean, na.rm=T)
    length(TAS.nppH.40pres)
    plot(t1000Hvec,TAS.nppH.40pres, type="l")
    
    ## calculate all Ks as relative to current
    nppH.AUS.rel <- AUS.nppH.array.40pres
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      nppH.AUS.rel[,,z] <- AUS.nppH.array.40pres[,,z] / AUS.nppH.array.40pres[,,1]
    }
    nppH.AUS.rel[,,1] <- AUS.nppH.array.40pres[,,1]
    
    nppH.TAS.rel <- TAS.nppH.array.40pres
    for (z in 1:dim(TAS.nppH.array.40pres)[3]) {
      nppH.TAS.rel[,,z] <- TAS.nppH.array.40pres[,,z] / TAS.nppH.array.40pres[,,1]
    }
    nppH.TAS.rel[,,1] <- TAS.nppH.array.40pres[,,1]
    
    # npp to K
    hum.dens.med <- 6.022271e-02
    hum.dens.lq <- 3.213640e-02
    hum.dens.uq <- 1.439484e-01
    hum.dens.max <- 1.152206e+00
    hum.dens.min <- 1.751882e-02
    cell.area <- (111.12/2)*(111.12/2) # km2
    
    # modify underlying K magnitude by modifying NPP across the board
    K.array <- nppH.AUS.rel
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      K.array[,,z] <- rscale(AUS.nppH.array.40pres[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(AUS.nppH.array.40pres[,,z], na.rm=T), max(AUS.nppH.array.40pres[,,z], na.rm=T))
    }

    # 180-deg rotated parabola
    # y = a(x - h)^2 + k
    # h = median NPP; k = max K; a = negative for 180 flipped
    k.Kmax <- max(K.array, na.rm=T)/2
    h.NPPmed <- mean(AUS.nppH.array.40pres, na.rm=T)
    h.NPPmed <- mean(range(AUS.nppH.array.40pres, na.rm=T))
    Kmin <- min(K.array, na.rm=T)
    NPP.seq <- seq(min(AUS.nppH.array.40pres, na.rm=T), max(AUS.nppH.array.40pres, na.rm=T), 0.01)
    K.parab.pred <- (-3 * (NPP.seq - h.NPPmed)^2) + k.Kmax
    K.parab.pred.rescale <- rscale(K.parab.pred, round(hum.dens.min*cell.area, 0), 0.5*round(hum.dens.max*cell.area, 0), min(K.parab.pred), max(K.parab.pred))

    K.lin.x <- c(min(AUS.nppH.array.40pres, na.rm=T), max(AUS.nppH.array.40pres, na.rm=T))
    K.lin.y <- c(min(K.array, na.rm=T), max(K.array, na.rm=T))
    fit.K.lin <- lm(K.lin.y ~ K.lin.x)
    K.lin.pred <- as.numeric(coef(fit.K.lin)[1]) + as.numeric(coef(fit.K.lin)[2])*NPP.seq
    
    # rotated parabolic
    K.array.parab <- (-3 * (AUS.nppH.array.40pres - h.NPPmed)^2) + k.Kmax
    K.array.parab.rescale <- K.array.parab
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      K.array.parab.rescale[,,z] <- rscale(K.array.parab[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(K.array.parab[,,z], na.rm=T), max(K.array.parab[,,z], na.rm=T))
    }

    # rescale so that parabolic total K = linear total K
    hist.K.array <- hist(K.array, br=12)
    hist.K.array.dat <- data.frame(hist.K.array$mids, hist.K.array$density)
    
    # rescale K.array.parab.rescale to same sum as K.array (distribution of Ks = same total)
    K.array.parab.rescale2 <- K.array.parab.rescale / (sum(K.array.parab.rescale, na.rm=T)/sum(K.array, na.rm=T))
    dim(K.array.parab.rescale2)
    sum(K.array.parab.rescale2, na.rm=T)
    
    hist.K.parab.pred.rescale2 <- hist(K.parab.pred.rescale2,br=12)
    hist.K.parab.pred.rescale2.dat <- data.frame(hist.K.parab.pred.rescale2$mids, hist.K.parab.pred.rescale2$density)

    # rotate matrix -90 & renumber from oldest to youngest
    if (K.NPP == "rotated parabolic") {
      K.array.use <- K.array.parab.rescale
    }
    
    K.rot.array <- array(data=NA, c(dim(K.array.use)[2], dim(K.array.use)[1], lzH))
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      K.rot.array[,,z] <- apply(t(K.array.use[,,42-z]),2,rev)
    }
    image(rot.mat(K.rot.array[,,41]))

    # population estimate 
    dim(K.rot.array)
    Kmod.array <- K.rot.array[,,41]
    sum(K.rot.array[,,41], na.rm=T)
    image(rot.mat(Kmod.array))

    # Tasmania estimate
    dim(K.rot.array)
    image(rot.mat(K.rot.array[60:64, 69:77, 41]))
    round(sum(K.rot.array[60:64, 69:77, 41], na.rm=T), 0)
    
    ## create & export rasters
    lat.vec <- -seq(11.5,43,0.5)
    lon.vec <- seq(110.5,153.5,0.5)
    llat <- length(lat.vec)
    llon <- length(lon.vec)
    llat*llon
    dim(Kmod.array)[1] * dim(Kmod.array)[2] 
    
    Kxyz <- matrix(data=NA,nrow=1,ncol=3)
    for (i in 1:llat) {
      for (j in 1:llon) {
        Kxyz <- rbind(Kxyz, c(lon.vec[j],lat.vec[i],Kmod.array[i,j]))
      }
    }
    
    Kxyz <- Kxyz[-1,]
    K.xyz <- as.data.frame(Kxyz)
    colnames(K.xyz) <- c("x","y","K")
    head(K.xyz)
    K.rast <- rasterFromXYZ(K.xyz, crs=CRS("+proj=longlat +datum=WGS84"))
    plot((K.rast))
    writeRaster(K.rast, filename="KparaMod.grd", format="raster", overwrite=T)
    
    Nprp.xyz <- data.frame("x"=K.xyz$x, "y"=K.xyz$y, "Nprp"=K.xyz$K/(sum(K.xyz$K, na.rm=T)))
    head(Nprp.xyz)
    hist(Nprp.xyz$Nprp)
    
    N2M.xyz <- data.frame("x"=K.xyz$x, "y"=K.xyz$y, "N2M"=2e6*Nprp.xyz$Nprp)
    N3M.xyz <- data.frame("x"=K.xyz$x, "y"=K.xyz$y, "N2M"=3e6*Nprp.xyz$Nprp)
    
    write.csv(N2M.xyz, "N2Mxyz.csv")
    write.csv(N3M.xyz, "N3Mxyz.csv")
    
    N2M.rast <- rasterFromXYZ(N2M.xyz, crs=CRS("+proj=longlat +datum=WGS84"))
    plot((N2M.rast))
    writeRaster(N2M.rast, filename="N2M.grd", format="raster", overwrite=T)
    
    N3M.rast <- rasterFromXYZ(N3M.xyz, crs=CRS("+proj=longlat +datum=WGS84"))
    plot((N3M.rast))
    writeRaster(N3M.rast, filename="N3M.grd", format="raster", overwrite=T)
    
    ## SAHUL
    ## calculate all Ks as relative to current
    nppH.rel <- nppH.array.40pres
    for (z in 1:dim(nppH.array.40pres)[3]) {
      nppH.rel[,,z] <- nppH.array.40pres[,,z] / nppH.array.40pres[,,1]
    }
    nppH.rel[,,1] <- nppH.array.40pres[,,1]
    
    # modify underlying K magnitude by modifying NPP across the board
    K.array <- nppH.rel
    for (z in 1:dim(nppH.array.40pres)[3]) {
      K.array[,,z] <- rscale(nppH.array.40pres[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(nppH.array.40pres[,,z], na.rm=T), max(nppH.array.40pres[,,z], na.rm=T))
    }
    
    # 180-deg rotated parabola
    # y = a(x - h)^2 + k
    # h = median NPP; k = max K; a = negative for 180 flipped
    k.Kmax <- max(K.array, na.rm=T)/2
    h.NPPmed <- mean(nppH.array.40pres, na.rm=T)
    h.NPPmed <- mean(range(nppH.array.40pres, na.rm=T))
    Kmin <- min(K.array, na.rm=T)
    NPP.seq <- seq(min(nppH.array.40pres, na.rm=T), max(nppH.array.40pres, na.rm=T), 0.01)
    K.parab.pred <- (-3 * (NPP.seq - h.NPPmed)^2) + k.Kmax
    K.parab.pred.rescale <- rscale(K.parab.pred, round(hum.dens.min*cell.area, 0), 0.5*round(hum.dens.max*cell.area, 0), min(K.parab.pred), max(K.parab.pred))
    
    K.lin.x <- c(min(nppH.array.40pres, na.rm=T), max(nppH.array.40pres, na.rm=T))
    K.lin.y <- c(min(K.array, na.rm=T), max(K.array, na.rm=T))
    fit.K.lin <- lm(K.lin.y ~ K.lin.x)
    K.lin.pred <- as.numeric(coef(fit.K.lin)[1]) + as.numeric(coef(fit.K.lin)[2])*NPP.seq
    
    # rotated parabolic
    K.array.parab <- (-3 * (nppH.array.40pres - h.NPPmed)^2) + k.Kmax
    K.array.parab.rescale <- K.array.parab
    for (z in 1:dim(nppH.array.40pres)[3]) {
      K.array.parab.rescale[,,z] <- rscale(K.array.parab[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(K.array.parab[,,z], na.rm=T), max(K.array.parab[,,z], na.rm=T))
    }
    
    # rescale so that parabolic total K = linear total K
    hist.K.array <- hist(K.array, br=12)
    hist.K.array.dat <- data.frame(hist.K.array$mids, hist.K.array$density)
    
    # rescale K.array.parab.rescale to same sum as K.array (distribution of Ks = same total)
    K.array.parab.rescale2 <- K.array.parab.rescale / (sum(K.array.parab.rescale, na.rm=T)/sum(K.array, na.rm=T))
    sum(K.array.parab.rescale2, na.rm=T)
    
    K.parab.pred.rescale2 <- K.parab.pred.rescale / (sum(K.array.parab.rescale, na.rm=T)/sum(K.array, na.rm=T))
    hist.K.parab.pred.rescale2 <- hist(K.parab.pred.rescale2,br=12)
    hist.K.parab.pred.rescale2.dat <- data.frame(hist.K.parab.pred.rescale2$mids, hist.K.parab.pred.rescale2$density)
    
    # rotate matrix -90 & renumber from oldest to youngest
    if (K.NPP == "rotated parabolic") {
      K.array.use <- K.array.parab.rescale
    }
    
    K.rot.array <- array(data=NA, c(dim(K.array.use)[2], dim(K.array.use)[1], lzH))
    for (z in 1:dim(nppH.array.40pres)[3]) {
      K.rot.array[,,z] <- apply(t(K.array.use[,,42-z]),2,rev)
    }
    
    # population estimate 
    Kmod.array <- K.rot.array[,,1]
    sum(K.rot.array[,,1], na.rm=T)
    
    
    ################################################################################   
    ## historically reported population sizes vs. carrying capacity-predicted sizes
    ################################################################################   
    
    # 10, 59
    # -17.067, 139.497 (Bentinck Island, Carpentaria) # Tindale 1962
    # 1910-1940: 103 to 123 people
    BI.crds <- rbind(coordlist2xyz(list(34, 59))) # Bentinck Island
    BI.K.cell <- K.rot.array[BI.crds[1,1], BI.crds[1,2], 1]
    BI.K.cell
    round(150/cell.area * BI.K.cell, 0)
    
    BI.cellN <- 3491
    BI.cellD <- BI.cellN/cell.area
    BI.predN <- BI.cellD * 150
    round(BI.predN, 0)
    
    # -40.692, 144.944 (Robbins Island, Tasmania): 50 people (Kelly in 1816, Baudin 1964)
    RI.crds <- rbind(coordlist2xyz(list(82, 70)))
    RI.K.cell <- K.rot.array[RI.crds[1,1], RI.crds[1,2], 1]
    RI.K.cell
    round(99/cell.area * RI.K.cell, 0)
    
    # -33.993, 151.17 (Botany Bay, NSW) # from Shane Ingrey: 400 people 
    BB.crds <- rbind(coordlist2xyz(list(68, 82)))
    BB.K.cell <- K.rot.array[BB.crds[1,1], BB.crds[1,2], 1]
    BB.K.cell
    round(416/cell.area * BB.K.cell, 0)
    
    BB.cellN <- 3548
    BB.cellD <- BB.cellN/cell.area
    BB.predN <- BB.cellD * 416
    round(BB.predN, 0)
    
    
    # -25.802, 113.025 (Dorre & Bernier Islands, WA); 100 km2, 40 people
    DH.crds <- rbind(coordlist2xyz(list(52, 7)))
    DH.K.cell <- K.rot.array[DH.crds[1,1], DH.crds[1,2], 1]
    DH.K.cell
    round(100/cell.area * DH.K.cell, 0)
    
    DBI.cellN <- 1331
    DBI.cellD <- DBI.cellN/cell.area
    DBI.predN <- DBI.cellD * 100
    round(DBI.predN, 0)
    
    # Botany Bay Kurnel Meeting Place -34 00 09" / 151 13" 15.6" ("no more than forty")
    # 24.11 km2; First Fleet observation
    # 34+(9/60/60) = -34.0025; 151+(13/60)+(15.6/(60*60)) = 151.221
    BBKMP.crds <- rbind(coordlist2xyz(list(68, 82)))
    BBKMP.K.cell <- K.rot.array[BBKMP.crds[1,1], BBKMP.crds[1,2], 1]
    BBKMP.K.cell
    round(24.11/cell.area * BBKMP.K.cell, 0)
    
    BBKMP.cellN <- 3548
    BBKMP.cellD <- BBKMP.cellN/cell.area
    BBKMP.predN <- BBKMP.cellD * 24.11
    round(BBKMP.predN, 0)
    
    # Sydney Cove
    # "Their number in the neighbourhood of this settlement, that is within ten miles (16 km) to
    # the northward and ten miles to the southward, I reckon at fifteen hundred.
    # Governor Phillip to Lord Sydney, 10 July 1788, in Historical Records of Australia,
    # Volume 1, 1788-1796, Governor's Despatches to and from England
    # (Sydney: The Library Committee of the Commonwealth Parliament, 1914), p. 65.
    # 151.2200032,	-33.86924628; area with 16 km buffer = 111.32^2 * 0.03944372784279604 = 489
    SC.cellN <- 3548
    SC.cellD <- SC.cellN/cell.area
    SC.predN <- SC.cellD * 489
    round(SC.predN, 0)
    
    # Possession Island, -10.72 / 142.40, 10 men, 5 km2 (Flinders referencing Cook)
    PI.crds <- rbind(coordlist2xyz(list(22, 64)))
    PI.K.cell <- K.rot.array[PI.crds[1,1], PI.crds[1,2], 1]
    PI.K.cell
    round(5/cell.area * PI.K.cell, 0)
    
    PI.cellN <- 3001
    PI.cellD <- PI.cellN/cell.area
    PI.predN <- PI.cellD * 5
    round(PI.predN, 0)
    
    # Darling (Erub) Island -9.59, 143.76, 5.7 km2, 80-90 people (Flinders 1803)
    EI.crds <- rbind(coordlist2xyz(list(19, 68)))
    EI.K.cell <- K.rot.array[EI.crds[1,1], EI.crds[1,2], 1]
    EI.K.cell
    round(5.7/cell.area * EI.K.cell, 0)

    
    ############################
    # analysis of Binford data #
    ############################
    
    bindens <- data.frame("GN"=LRB$groupno, "year"=LRB$year, "lon"=LRB$longitude, "lat"=LRB$latitude, "area"=LRB$area,
                          "pdens"=LRB$density/100)
    write.table(bindens, "bindens.csv", sep=",", row.names = F)
    
    bindensModOverl <- read.csv("bindensModelOverlay.csv")
    
    plot(bindensModOverl$pdens, bindensModOverl$modD, pch=19, ylab="model", xlab="Binford", xlim=c(0,1.2), ylim=c(0,1.2))
    bindensMod.fit <- lm(modD ~ pdens, data=bindensModOverl)
    summary(bindensMod.fit)    
    abline(bindensMod.fit, col="red", lty=2, lwd=2)
    xy121 <- data.frame("x"=seq(0,1.2,0.01), "y"=seq(0,1.2,0.01))
    lines(xy121[,1],xy121[,2], lty=2, lwd=2)
    range(bindensModOverl$year)
    median(bindensModOverl$year)
    
    hist(bindensModOverl$pdens)
    hist(bindensModOverl$modD)
    
    bindensModOverl$DratioM2B <- bindensModOverl$modD/bindensModOverl$pdens
    hist((bindensModOverl$DratioM2B))
    hist(log10(bindensModOverl$DratioM2B))
    1/exp(mean(log(bindensModOverl$DratioM2B)))
    
    # generalised linear models
   
    head(bindensModOverl)
    hist(bindensModOverl$year)
    plot(bindensModOverl$year, bindensModOverl$pdens, xlab="year", ylab="Binford D", pch=19)
    plot(bindensModOverl$year, (bindensModOverl$DratioM2B), xlab="year", ylab="model D:Binford D", pch=19)
    
    # model set
    m1 <- "pdens ~ modD + year"
    m2 <- "pdens ~ modD"
    m3 <- "pdens ~ year"
    m4 <- "pdens ~ 1"
    
    ## model vector
    mod.vec <- c(m1,m2,m3,m4)
    length(mod.vec)
    length(unique(mod.vec))
    
    ## define n.mod
    n.mod <- length(mod.vec)
    
    # model fitting and logLik output loop
    Modnum <- length(mod.vec)
    LL.vec <- SaveCount <- AICc.vec <- BIC.vec <- k.vec <- terml <- Rm <- Rc <- rep(0,Modnum)
    mod.list <- summ.fit <- coeffs <- coeffs.se <- term.labs <- coeffs.st <- list()
    mod.num <- seq(1,Modnum,1)
    
    for(i in 1:Modnum) {
      fit <- glm(as.formula(mod.vec[i]),family=gaussian(link="log"), data=bindensModOverl, na.action=na.omit)
      assign(paste("fit",i,sep=""), fit)
      mod.list[[i]] <- fit
      print(i)
    }
    
    sumtable <- aicW(mod.list, finite = TRUE, null.model = NULL, order = F)
    row.names(sumtable) <- mod.vec
    summary.table <- sumtable[order(sumtable[,7],decreasing=F),]
    summary.table
    
    ## saturated residual diagnostic
    i <- 1
    fit <- glm(as.formula(mod.vec[i]),family=gaussian(link="log"), data=bindensModOverl, na.action=na.omit)

    check_model(fit, detrend=F)
    plot_model(fit, show.values=T, vline.color = "purple")
    
    # BRT
    dim(bindensModOverl)[1]
    hist(bindensModOverl$DratioM2B)
    bindensModOverl$DratioM2B.sc <- scale(bindensModOverl$DratioM2B, center=T, scale=T)
    bindensModOverl$DratioM2B.lg10 <- log10(bindensModOverl$DratioM2B)
    bindensModOverl$neglat.sc <- scale(-bindensModOverl$lat, center=T, scale=T)
    bindensModOverl$year.sc <- scale(bindensModOverl$year, center=T, scale=T)
    head(bindensModOverl)
    
    brt.fit <- gbm.step(bindensModOverl, gbm.x = attr(bindensModOverl, "names")[c(2,4)],
                        gbm.y = attr(bindensModOverl, "names")[11], 
                        family="gaussian", max.trees=100000, tolerance = 0.0002, learning.rate = 0.00025, 
                        bag.fraction=0.75, tree.complexity = 2)
    summary(brt.fit)
    gbmpl <- gbm.plot(brt.fit, smooth=T, n.plots=2, common.scale=T, y.label="log10 model D:Binford D", plot.layout = c(1,2),
             show.contrib = T, rug=T)
    gbm.plot.fits(brt.fit)
    brt.fit$fitted.vars
    
    par(mfrow=c(1,2))
    x2 <- plot.gbm(brt.fit, i.var=brt.fit$var.names[2], continuous.resolution=100, return.grid=T)[,1]
    y2 <- 10^plot.gbm(brt.fit, i.var=brt.fit$var.names[2], continuous.resolution=100, return.grid=T)[,2]
    plot(x2,y2,type="l", xlab=brt.fit$var.names[2], ylab="model D:Binford D", ylim=c(0,40))
    x1 <- plot.gbm(brt.fit, i.var=brt.fit$var.names[1], continuous.resolution=100, return.grid=T)[,1]
    y1 <- 10^plot.gbm(brt.fit, i.var=brt.fit$var.names[1], continuous.resolution=100, return.grid=T)[,2]
    plot(x1,y1,type="l", xlab=brt.fit$var.names[1], ylab="model D:Binford D", ylim=c(0,40))
    par(mfrow=c(1,1))
    
    BRTmodDBinD.dat <- data.frame("latx"=x2, "laty"=y2, "yearx"=x1, "yeary"=y1)
    write.table(BRTmodDBinD.dat, "BRTmodDBinD.csv", sep=",", row.names = F)
    
    CV.cor <fitted.varsCV.cor <- 100 * brt.fit$cv.statistics$correlation.mean
    CV.cor.se <- 100 * brt.fit$cv.statistics$correlation.se
    print(c(CV.cor, CV.cor.se))
    
    

    ############################################################################################
    ## simple demographic model to estimate total mortality rate required to move from various
    ## pre-European estimates to the 1850 estimate of ~ 220 000
    ############################################################################################
    
    ## functions
    # beta distribution shape parameter estimator function
    estBetaParams <- function(mu, var) {
      alpha <- ((1 - mu) / var - 1 / mu) * mu ^ 2
      beta <- alpha * (1 / mu - 1)
      return(params = list(alpha = alpha, beta = beta))
    }

    
    # Siler hazard h(x) (Gurven et al. 2007)
    # average hunter-gatherer
    a1 <- 0.422 # initial infant mortality rate (also known as αt)
    b1 <- 1.131 # rate of mortality decline (also known as bt)
    a2 <- 0.013 # age-independent mortality (exogenous mortality due to environment); also known as ct
    a3 <- 1.47e-04 # initial adult mortality rate (also known as βt)
    b3 <- 0.086 # rate of mortality increase
    longev <- 80
    x <- seq(0,longev,1) # age vector
    h.x <- a1 * exp(-b1*x) + a2 + a3 * exp(b3 * x) # Siler's hazard model
    l.x <- exp((-a1/b1) * (1 - exp(-b1*x))) * exp(-a2 * x) * exp(a3/b3 * (1 - exp(b3 * x))) # Siler's survival (proportion surviving) model
    
    l.inf <- exp(-a1/b1) # survival at infinite time
    T.m <- 1/b1 # time constant at which maturity is approached
    h.m <- a2 # hazard for mature animals
    l.m <- exp(-a2*x) # survival
    h.s <- a3*exp(b3*x) # hazard for senescence
    l.s <- exp((a3/b3)*(1 - exp(b3*x))) # survival for senescence
    f.x <- a3*exp(b3*x)*exp((a3/b3)/(1-exp(b3*x))) # probability density function
    (log(a3) - log(a1)) / a3
    T.s <- (1/b3) # modal survival time
    
    ## survival
    init.pop <- 10000
    lx <- round(init.pop*l.x,0)
    len.lx <- length(lx)
    dx <- lx[1:(len.lx-1)]-lx[2:len.lx]
    qx <- dx/lx[1:(length(lx)-1)]
    Sx <- 1 - qx
    sx <- lx[2:len.lx]/lx[1:(len.lx-1)]
    mx <- 1 - sx
    Lx <- (lx[1:(len.lx-1)] + lx[2:len.lx])/2
    ex <- rev(cumsum(rev(Lx)))/lx[-len.lx]
    ex.avg <- ex + x[-len.lx]
    
    # set SD for Sx
    Sx.sd <- 0.05 # can set to any value
    
    # fertility (Walker et al. 2006)
    primiparity.walker <- c(17.7,18.7,19.5,18.5,18.5,18.7,25.7,19,20.5,18.8,17.8,18.6,22.2,17,16.2,18.4)
    prim.mean <- round(mean(primiparity.walker),0)
    prim.lo <- round(quantile(primiparity.walker,probs=0.025),0)
    prim.hi <- round(quantile(primiparity.walker,probs=0.975),0)
    
    dat.world13 <- read.table("world2013lifetable.csv", header=T, sep=",")
    fert.world13 <- dat.world13$m.f
    fert.trunc <- fert.world13[1:(longev+1)]
    pfert.trunc <- fert.trunc/sum(fert.trunc)
    fert.bentley <- 4.69/2 # Bentley 1985 for !Kung
    fert.vec <- fert.bentley * pfert.trunc
    fert.sd.vec <- 0.05*fert.vec
    
    ## construct matrix
    stages <- len.lx
    popmat <- matrix(0,nrow=stages,ncol=stages)
    colnames(popmat) <- x
    rownames(popmat) <- x
    
    ## populate matrix
    popmat[1,] <- fert.vec
    diag(popmat[2:stages,]) <- Sx
    popmat[stages,stages] <- 0 # Sx[stages-1]
    popmat.orig <- popmat ## save original matrix
    
    ## matrix properties
    max.lambda(popmat)
    r.ann <- max.r(popmat) # rate of population change, 1-yr
    #stable.stage.dist(popmat) ## stable stage distribution
    R.val(popmat,stages) # reproductive value
    gen.l <- G.val(popmat,stages) # mean generation length
    
    #stable.stage.dist(popmat) ## stable stage distribution
    R.val(popmat,stages) # reproductive value

    
    
    
    
    ## 5 million
    # initial population vector
    age.max <- 80
    pop.found <- 5000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                     data = Kred.dat,
                     algorithm = "port",
                     start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                     trace = TRUE,      
                     nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]

      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
   
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################

    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 41000, 500) # to 1861
    killed.pyr.vec <- seq(1000, 33000, 500) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    ## 4.5 million
    # initial population vector
    pop.found <- 4500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 3)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 38000, 500) # to 1861
    killed.pyr.vec <- seq(1000, 30000, 500) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    
    ## 4 million
    # initial population vector
    pop.found <- 4000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 35000, 200) # to 1861
    killed.pyr.vec <- seq(1000, 28000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    ## 3.5 million
    # initial population vector
    pop.found <- 3500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 28000, 500) # to 1861
    killed.pyr.vec <- seq(1000, 20000, 500) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    ## 3 million
    # initial population vector
    pop.found <- 3000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 25000, 200) # to 1861
    killed.pyr.vec <- seq(1000, 20000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    
    ## 2.5 million
    # initial population vector
    pop.found <- 2500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 3)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 19000, 200) # to 1861
    killed.pyr.vec <- seq(1000, 14000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    
    ## 2 million
    # initial population vector
    pop.found <- 2000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 16600, 200) # to 1861
    killed.pyr.vec <- seq(1000, 14000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    

    
        
    
    ## 1.5 million
    # initial population vector
    pop.found <- 1500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 3)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 11500, 100) # to 1861
    killed.pyr.vec <- seq(1000, 8500, 100) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    ## 1 million
    # initial population vector
    pop.found <- 1000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 8000, 50) # to 1861
    killed.pyr.vec <- seq(1000, 5000, 50) # to 1901
    
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1901
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1901
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))

    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    #####################################################
    ## bootstrapped mean range for modelled/Ne numbers
    #####################################################
    
    Nmd.npp <- 5222387 # NPP model
    Nmd.14C <- 1955000; Nlo.14C <- 1160000; Nup.14C <- 2750000 # Williams et al. 2013
    Nmd.TNe <- 1354000; Nlo.TNe <- 308000; Nup.TNe <- 2400000 # Tobler et al. 2017
    Nmd.MNe <- 2946970; Nlo.MNe <- 22960; Nup.MNe <- 5870980 # Malaspinas et al. 2017
    
    # sd
    Nse.14C <- ((Nmd.14C-Nlo.14C) + (Nup.14C-Nmd.14C))/2/1.96
    Nse.TNe <- ((Nmd.TNe-Nlo.TNe) + (Nup.TNe-Nmd.TNe))/2/1.96
    Nse.MNe <- ((Nmd.MNe-Nlo.MNe) + (Nup.MNe-Nmd.MNe))/2/1.96
    
    NCV.14C <- Nse.14C/Nmd.14C
    NCV.TNe <- Nse.TNe/Nmd.TNe
    NCV.MNe <- Nse.MNe/Nmd.MNe
    
    NCV.mn <- mean(c(NCV.14C,NCV.TNe,NCV.MNe))    
    Nse.npp.calc <- Nmd.npp*NCV.mn
    
    biter <- 10000
      Nrnd.npp <- round(rtruncnorm(biter, a=0, b=Nmd.npp, mean=Nmd.npp, sd=Nse.npp.calc), 0)
      Nrnd.14C <- round(rnorm(biter, mean=Nmd.14C, sd=Nse.14C), 0)
      Nrnd.TNe <- round(rnorm(biter, mean=Nmd.TNe, sd=Nse.TNe), 0)
      Nrnd.MNe <- round(rnorm(biter, mean=Nmd.MNe, sd=Nse.MNe), 0)
      
      Nrnd.all <- c(Nrnd.npp,Nrnd.14C,Nrnd.TNe,Nrnd.MNe)
      # Nrnd.all <- c(Nrnd.npp,Nrnd.14C,Nrnd.TNe) # without the Malaspinas estimate
      Nmn.boot <- median(Nrnd.all, na.rm=T)
      Nsd.boot <- sd(Nrnd.all, na.rm=T)
      Nmn.boot + Nsd.boot
      Nmn.boot - Nsd.boot
      Nlo.boot <- quantile(Nrnd.all, probs=0.125, na.rm=T) # lower 75th %ile
      Nup.boot <- quantile(Nrnd.all, probs=0.875, na.rm=T) # upper 75th %ile
      print(c(Nlo.boot, Nmn.boot, Nup.boot))
      
      NmedBS <- bootstrap(Nrnd.all, biter, theta=mean)$thetastar
      NmedBS.up <- quantile(NmedBS, probs=0.125, na.rm=T)
      NmedBS.lo <- quantile(NmedBS, probs=0.875, na.rm=T)
      NmedBS.md <- mean(NmedBS)
      print(c(NmedBS.lo, NmedBS.md, NmedBS.up))
      
area.aus <- 7688287 # km2
print(c(NmedBS.lo/area.aus, NmedBS.md/area.aus, NmedBS.up/area.aus))

      
##########################################
# projection to median pre-colonial size
##########################################

census.dat <- data.frame('year'=c(1971,1976,1981,1986,1991,1996,2001,2006,2011,2016,2021),
                         'N'=c(115953,160912,159897,227645,265459,352970,410003,455028,548368,649171,812728))
len.census.dat <- dim(census.dat)[1]
census.r <- log(census.dat$N[2:len.census.dat]/census.dat$N[1:(len.census.dat-1)]) / diff(census.dat$year)
census.r.mn <- mean(census.r)
census.r.mn
years.ahead <- seq(1,30)
N.proj <- round(census.dat$N[len.census.dat]*exp(census.r.mn*years.ahead), 0)
years.fut <- 2021+years.ahead
plot(years.fut, N.proj, type="l")
abline(h=2510000, lty=2, col="red")
target.N <- years.fut[which.min(abs(N.proj - 2510000))]
target.N
abline(v=target.N, lty=2, col="red")
