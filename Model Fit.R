#####Lyme Trends

#####Load Packages
library(BayesLogit)
library(car)
library(coda)
library(ExtDist)
library(ggplot2)
library(inline)
library(invgamma)
library(kriging)
library(maps)
library(MASS)
library(Matrix)
library(matrixcalc)
library(msm)
library(mvtnorm)
library(SDMTools)
library(snow)
library(sp)
library(rARPACK)
library(Rcpp)
library(rgdal)
library(rgl)
#library(SDMTools)
library(scatterplot3d)
library(sp)
library(SparseM)
library(truncnorm)

###Read in the Files and Rccp Functions
path = "C:/Users/scwatson/Stella Self Dropbox/Stella Watson/Synced Files/CAPC/Polya Gamma/Paper Applications/ReRuns for App Papers/Lyme/ReRun2013to2019/"
#path = "/home/stellaw/PG/"

idx<-read.csv(paste0(path,"borderingcounties.csv"))
ref.counties.raw = read.csv(paste0(path,"FIPSCodes.csv"),stringsAsFactors = FALSE,header = TRUE)
raw.Y = read.csv(paste0(path,'2509_2013_1-2019_12_dog_lyme disease_all.csv'),header = TRUE)
lld = read.csv(paste0(path,'countylatlong.csv'),stringsAsFactors = FALSE,header = TRUE)

#####Support Functions

#####Samples from an MVN Distribution
mvn.samp<-function(sig.mn,prec){
  n = length(sig.mn)
  prec = forceSymmetric(prec)
  L = t(chol(prec))
  v = forwardsolve(L,sig.mn)
  mu = backsolve(t(L),v)
  z = rnorm(n,0,1)
  y = backsolve(t(L),z)
  x = y + mu
  return(x)
}

#####Samples Gamma
gamma.samp<-function(g.c, sig.c, beta, C.Inv, Kap, Dist.Mat.K,Dist.Mat.Kappa, eta.star,H, w.g.D,X,eps,K,pv){
  s.c = log(g.c/(1-g.c))
  s.p = rnorm(1,s.c,pv^2)
  g.p = exp(s.p)/(1+exp(s.p))
  C.p.Inv = 1/sig.c*(solve(g.p^Dist.Mat.K + diag(eps,K)))
  Kap.p = sig.c*g.p^Dist.Mat.Kappa
  CK.p = C.p.Inv%*%t(Kap.p)
  CK = C.Inv%*%t(Kap)
  XBT.p = X%*%t(CK.p)%*%beta
  XBT = X%*%t(CK)%*%beta
  den.p = -(1/2)*(t(XBT.p)%*%w.g.D%*%XBT.p + 2*t(XBT.p)%*%w.g.D%*%eta.star - 2*t(H)%*%XBT.p)
  den.p = den.p + log(sqrt(det(C.p.Inv))) + (- (1/2)*t(beta)%*%C.p.Inv%*%beta)
  den.p = as.numeric(den.p + s.p - 2*log(1+exp(s.p)) ) #+  dbeta(g.p,85*10^(-3),15*10^(-3),log = TRUE))
  den.c = -(1/2)*(t(XBT)%*%w.g.D%*%XBT + 2*t(XBT)%*%w.g.D%*%eta.star - 2*t(H)%*%XBT)
  den.c = den.c + log(sqrt(det(C.Inv))) + (- (1/2)*t(beta)%*%C.Inv%*%beta)
  den.c = as.numeric(den.c +  s.c - 2*log(1+exp(s.c)) )#+  dbeta(g.c,85*10^(-3),15*10^(-3),log = TRUE))
  a = min(1,exp(den.p-den.c + dnorm(s.c,mean = s.p,pv^2,log = TRUE) - dnorm(s.p,mean = s.c,pv^2,log = TRUE)))
  r = rbinom(1,1,a)
  res = r*g.p + (1-r)*g.c
  return(c(res,r,den.c))
}

#####Samples Omega
omega.samp<-function(oc,ovar,tau,D,W,xi,zeta,A,t,ev){
  qc = log(oc/(1-oc))
  qp = rnorm(1,qc,ovar^2 )
  op = exp(qp)/(1+exp(qp))
  #op = runif(1,0.01,0.99)
  B.p = D - op*W
  A.p = 1/tau*B.p
  ev.p = 1 - op*ev
  ev.c = 1 - oc*ev
  #prop/cur
  det.ratio = (t/2)*log(abs((prod(ev.c)/prod(ev.p))))
  tb = xi.g[,1]%*%A%*%xi.g[,1]
  tb.p = xi.g[,1]%*%A.p%*%xi.g[,1]
  for(ip in 2:t){
    tb.p = tb.p + t(xi.g[,ip] - zeta*xi.g[,ip-1])%*%A.p%*%(xi.g[,ip] - zeta*xi.g[,ip-1])
    tb = tb + t(xi.g[,ip] - zeta*xi.g[,ip-1])%*%A%*%(xi.g[,ip] - zeta*xi.g[,ip-1])
  }
  den.c = -1/2*tb + dbeta(oc,900,100,log = TRUE)
  den.p = -1/2*tb.p + dbeta(op,900,100,log = TRUE)
  den.p = den.p + qp -2* log(1 + exp(qp))
  den.c = den.c + qc -2* log(1 + exp(qc))
  a = min(1, as.numeric(exp(det.ratio + den.p-den.c)))
  r = rbinom(1,1,a)
  res = r*op + (1-r)*oc
  return(c(res,r))
}

###Parameters
###MCMC Interations and burn in
G = 30000
burn =20000
###Number of Knots
K=100
eps = 0.01

###Hyperparameters
alpha = 2
delta = 2
a_tau = 2
b_tau = 2
zeta.m = 0
zeta.s = 10
upsilon.s = 1000

###Clean Response Data
main.df = data.frame(0,0,0,0)
main.df = main.df[-1,]
month.abbrev.list = c("Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec")
year.abbrev.list = c("2013","2014","2015","2016","2017","2018","2019")
yr = length(year.abbrev.list)
t = 84
test.string.list = c()
positive.string.list = c()
for(i in 1:(yr-1)){
  for(j in 1:12){
    test.string.list = c(test.string.list,paste0("X.test",month.abbrev.list[j],"_",year.abbrev.list[i],"."))
    positive.string.list = c(positive.string.list,paste0("X.positive",month.abbrev.list[j],"_",year.abbrev.list[i],"."))
  }
}
for(i in yr){
  for(j in 1:12){
    test.string.list = c(test.string.list,paste0("X.test",month.abbrev.list[j],"_",year.abbrev.list[i],"."))
    positive.string.list = c(positive.string.list,paste0("X.positive",month.abbrev.list[j],"_",year.abbrev.list[i],"."))
  }
}
for(i in 1:t){
  test.id = test.string.list[i]
  positive.id = positive.string.list[i]
  id = which((!is.na(raw.Y[,test.id]))& raw.Y[,test.id] >0 )
  val.mat = cbind(raw.Y$X.FIPS.[id],i,raw.Y[id,positive.id],raw.Y[id,test.id])
  main.df = rbind(main.df,val.mat)
}
names(main.df) = c("FIPS","Month","Positives","Tests")
###Pull Out Alaska and Hawaii
ind = main.df$FIPS>=2000 & main.df$FIPS < 3000
main.df = main.df[!ind,]
ind = main.df$FIPS>=15000 & main.df$FIPS < 16000
main.df = main.df[!ind,]
n= sum(main.df$Tests)
nct = dim(main.df)[1]

###Create CAR matrices
nd<-dim(idx)[1]
out<-rep(0,nd)
for(i in 1:nd){
  out[i]<-(gsub("\\D", "", idx[i,]))
}
ct = c(which(nchar(out)==10))
ctt = c(which(nchar(out)==10),nd+1)
head = rep(0,length(ct))
nber = list()
ii=1
for(i in ct){
  a = substring(out[i],c(1,6),c(5,10))
  head[ii]<-a[1]
  rg = seq(ct[ii]+1,ctt[ii+1]-1)
  nber[[ii]]= c(a[2],out[rg])
  nber[[ii]] = nber[[ii]][!nber[[ii]] %in% head[ii]]
  ii=ii+1
}
head = as.numeric(head)

###Sorts Though County FIPS
ref.counties.raw = ref.counties.raw[ref.counties.raw[,1]!="AK",]
ref.counties.raw = ref.counties.raw[ref.counties.raw[,1]!="HI",]
ref.counties= cbind(ref.counties.raw[,1],ref.counties.raw[,10])
ind = !(duplicated(ref.counties))
ref.counties = ref.counties.raw[ind,c(1,4,10)]

### generate the adjacency matrix
S=dim(ref.counties)[1]
W=matrix(0,ncol=S,nrow=S)
###### first order neighbor
for(i in 1:S){
  hd = match(ref.counties[i,3],head)
  id_j = match(as.numeric(nber[[hd]]),ref.counties[,3])
  W[i,id_j] = 1
  W[id_j,i] = 1
}
isSymmetric(W) # check is symmetric
ind = W!=0
r.mat = row(W)
c.mat = col(W)
r.ind = r.mat[ind]
c.ind = c.mat[ind]
x.vals = W[ind]
W= sparseMatrix(i = r.ind, j = c.ind, x = x.vals)
#write.csv(as.matrix(W),paste0(path,"WRD.csv"))
#colSums(W)
D = sparseMatrix(i = seq(1,S,by = 1), j = seq(1,S,by = 1),x =colSums(W))
D.diag = colSums(W)
### get W.adj matrix
W.adj = matrix(0,nrow=S,ncol=max(D.diag)+1)
for(i in 1:S){
  W.adj[i,1] = D.diag[i]
  nonzero = which(W[i,]!=0)
  W.adj[i,seq(2,1+length(nonzero))] = nonzero
}
D.I.Sq = sparseMatrix(i = seq(1,S, by = 1), j = seq(1, S, by = 1), x = 1/sqrt(D.diag))
evals = eigen(D.I.Sq%*%W%*%D.I.Sq)$values

###Create IDS for CGS
id<-1:S
id.grp1<-NULL
id.rem1<-NULL
for(i in 1:S){
  if(sum(id[i]==id.rem1)==0){
    id.grp1<-c(id.grp1,id[i])
    id.rem1<-c(id.rem1,id[W[id[i],]==1])
  }
}
id.grp2<-NULL
id.rem2<-id.grp1
for(i in 1:S){
  if(sum(id[i]==id.rem2)==0){
    id.grp2<-c(id.grp2,id[i])
    id.rem2<-c(id.rem2,id[W[id[i],]==1])
  }
}
id.grp3<-NULL
id.rem3<-c(id.grp1,id.grp2)
for(i in 1:S){
  if(sum(id[i]==id.rem3)==0){
    id.grp3<-c(id.grp3,id[i])
    id.rem3<-c(id.rem3,id[W[id[i],]==1])
  }
}
id.grp4<-NULL
id.rem4<-c(id.grp1,id.grp2,id.grp3)
for(i in 1:S){
  if(sum(id[i]==id.rem4)==0){
    id.grp4<-c(id.grp4,id[i])
    id.rem4<-c(id.rem4,id[W[id[i],]==1])
  }
}
id.grp5<-NULL
id.rem5<-c(id.grp1,id.grp2,id.grp3,id.grp4)
for(i in 1:S){
  if(sum(id[i]==id.rem5)==0){
    id.grp5<-c(id.grp5,id[i])
    id.rem5<-c(id.rem5,id[W[id[i],]==1])
  }
}
id.grp6<-NULL
id.rem6<-c(id.grp1,id.grp2,id.grp3,id.grp4,id.grp5)
for(i in 1:S){
  if(sum(id[i]==id.rem6)==0){
    id.grp6<-c(id.grp6,id[i])
    id.rem6<-c(id.rem6,id[W[id[i],]==1])
  }
}
id.grp7<-NULL
id.rem7<-c(id.grp1,id.grp2,id.grp3,id.grp4,id.grp5,id.grp6)
for(i in 1:S){
  if(sum(id[i]==id.rem7)==0){
    id.grp7<-c(id.grp7,id[i])
    id.rem7<-c(id.rem7,id[W[id[i],]==1])
  }
}

###Generate the Distance matrices
###Load the lat and long
lld = lld[!(is.na(lld[,1])),]
colnames(lld) = c(colnames(lld)[1:7],"FIPS")
ind = is.element(lld$FIPS,ref.counties$FIPS)
lld = lld[ind,]
###S by S
Lat = lld$LATITUDE
Long = lld$LONGITUDE
Dist.Mat = matrix(99,S,S)
for(i in 1:S){
  lat.i = Lat[i]
  long.i = Long[i]
  dist = sqrt((Lat - lat.i)^2 + (Long - long.i)^2)
  Dist.Mat[i,] = dist
}
dist.scale = max(Dist.Mat)/10
Dist.Mat = Dist.Mat/dist.scale

###K by K
knots = kmeans(x = cbind(Lat,Long),centers = K)
Lat.K = knots$centers[,1]
Long.K = knots$centers[,2]
K = length(Long.K)

Dist.Mat.K = matrix(99,K,K)
for(i in 1:K){
  lat.i = Lat.K[i]
  long.i = Long.K[i]
  dist = sqrt((Lat.K - lat.i)^2 + (Long.K - long.i)^2)
  Dist.Mat.K[i,] = dist
}
Dist.Mat.K = Dist.Mat.K/dist.scale

###K by S
Dist.Mat.Kappa = matrix(99,S,K)
for(i in 1:K){
  lat.i = Lat.K[i]
  long.i = Long.K[i]
  dist = sqrt((Lat - lat.i)^2 + (Long - long.i)^2)
  Dist.Mat.Kappa[,i] = dist
}
Dist.Mat.Kappa = Dist.Mat.Kappa/dist.scale

###Format the Covariate Data
S = length(unique(ref.counties.raw$FIPS))
main.df = main.df[is.element(main.df$FIPS,ref.counties$FIPS),]
mi = main.df$tests
p = 1
nct = dim(main.df)[1]

##Construct the Sparse Matrix
row.i = seq(1,nct,by=1)
col.i = rep(0,nct)
xvals = rep(99,nct)
for(i in 1:S){
  fips.i = ref.counties$FIPS[i]
  ind = main.df$FIPS==fips.i
  col.i[ind] = i
  xvals[ind] = main.df$Month[ind]
  print(i)
}
xvals = xvals/t

mat.list = list(rep(0,p))
mat.list[[1]] = sparseMatrix(i=row.i, j = col.i,x=xvals,dims=c(nct,S))

Q = 1
U = matrix(1,nct,1)

ind.list = list()
for(i in 1:t){
  t.i = rep(FALSE,nct)
  ind = which(main.df$Month==i)
  t.i[ind] = TRUE
  ind.list[[i]] = t.i
  print(i)
}
# 
# ###Make G Matrix
r.i = seq(1,nct,by = 1)
xv = rep(1,nct)
ci = rep(-99,nct)
for(i in 1:t){
  for(j in 1:S){
    fi = ref.counties$FIPS[j]
    ind = which(main.df$FIPS == fi & main.df$Month==i)
    if(length(ind) >0){
      ci[ind] = (i-1)*S + j
    }
  }
  print(i)
}

G.Mat = sparseMatrix(i = r.i, j = ci, x = xv, dims = c(nct,S*t))

G.mat.list = list()
for(i in 1:t){
  ind = which(ci > (i-1)*S & ci <= i*S)
  nob = length(ind)
  ri = seq(1,nob, by = 1)
  xv = rep(1,nob)
  c.i = ci[ind] -  (i-1)*S
  G.mat.list[[i]] = sparseMatrix(i = ri, j = c.i, x = xv, dims = c(nob,S))
  print(i)
}

###Initialization
mi = main.df$Tests
Y = main.df$Positives
H = Y - mi/2

###Sampling Loop
acc.gamma = rep(0,p)
acc.omega = 0
sig.g = 1
sig.in = rep(sig.g,p)
gamma.g = .9
gamma.in = rep(gamma.g,p)
tau.g = 0.005
omega.g = 0.999
xi.g = matrix(0,S,t)
zeta.g = 0.95
A = 1/tau.g*(D - omega.g*W)
g.var = rep(0.5,p)
omega.var = 1
g.save = 5
g.s =1
xi.array = array(99,c(S,t,G/g.save))
zeta.array = array(99,c(1,1,G))
tau.array = array(99,c(1,1,G))
omega.array = array(99,c(1,1,G))
beta.g = matrix(0,K,p)
beta.tilde = matrix(0,S,p)
upsilon.g = -4
beta.array = array(99,c(K,p,G))
beta.tilde.array = array(99,c(S,p,G))
sig.array = array(99,c(1,p,G))
gamma.array = array(99,c(1,p,G))
upsilon.array = array(99,c(1,Q,G))
beta.array[,,1] = beta.g
beta.tilde.array[,,1] = beta.tilde
sig.array[1,,1] = sig.in
gamma.array[1,,1] = gamma.in
upsilon.array[1,,1] = upsilon.g
xi.array[,,1] = xi.g
zeta.array[,1,1] = zeta.g
tau.array[1,1,1] = tau.g
omega.array[1,1,1] = omega.g
XTX.diag = list()
for(j in 1:p){
  XTX.diag = c(XTX.diag,t(mat.list[[j]])%*%mat.list[[j]])
}
G.T.G.Mat.List = list()
for(i in 1:t){
  G.T.G.Mat.List[[i]] = t(G.mat.list[[i]])%*%G.mat.list[[i]]
}
UTU = t(U)%*%U
Sig.upsilon = solve(UTU + 1/upsilon.s*diag(Q))

###Sampling Loop
start.time = Sys.time()
g.s = 1
for(g in 2:G){
  XB = rep(0,nct)
  for(i in 1:p){
    XB = XB + mat.list[[i]]%*%beta.tilde[,i]
  }
  eta.g = as.vector(XB+ G.Mat%*%as.vector(xi.g))
  eta.g = as.vector(eta.g + U%*%upsilon.g)
  w.g = rpg(nct,as.numeric(mi),as.numeric(eta.g))
  w.g.D = sparseMatrix(i = seq(1,nct,by = 1), j = seq(1,nct,by = 1), x = w.g)
  for(i in 1:p){
    gamma.g = gamma.array[1,i,(g-1)]
    sig.g = sig.array[1,i,(g-1)]
    eta.star = rep(0,nct)
    for(j in 1:p){
      if(j!=i){
        eta.star = eta.star + mat.list[[j]]%*%beta.tilde[,j]
      }
    }
    eta.star = eta.star + G.Mat%*%as.vector(xi.g)
    eta.star = eta.star + U%*%upsilon.g
    D.k.inv = solve(gamma.g^Dist.Mat.K + diag(eps,K))
    C.k.Inv =1/sig.g*D.k.inv
    Kappa.k = sig.g*(gamma.g^Dist.Mat.Kappa)
    CKap = Kappa.k%*%C.k.Inv
    XPX = t(mat.list[[i]])%*%w.g.D%*%mat.list[[i]]
    Sig.k.Inv = t(CKap)%*%XPX%*%CKap + C.k.Inv
    Sig.k.Inv = 1/2*(Sig.k.Inv+t(Sig.k.Inv))
    CKX = t(CKap)%*%t(mat.list[[i]])
    Sig.mu.k = CKX%*%(-1*w.g.D%*%eta.star + H)
    beta.g = mvn.samp(Sig.mu.k, Sig.k.Inv)
    beta.tilde[,i] = Kappa.k%*%C.k.Inv%*%beta.g
    beta.tilde.array[,i,g] = beta.tilde[,i]
    beta.array[,i,g] = beta.g
    sig.g = rinvgamma(1,shape = K/2+alpha, rate = delta + (1/2)*t(beta.g)%*%D.k.inv%*%beta.g )
    #Recalculate with New Sigma
    C.k.Inv =1/sig.g*D.k.inv
    Kappa.k = sig.g*gamma.g^Dist.Mat.Kappa
    gamma.list = gamma.samp(gamma.g, sig.g, beta.g, C.k.Inv, Kappa.k, Dist.Mat.K, Dist.Mat.Kappa,eta.star,H,w.g.D,mat.list[[i]],eps, K, g.var[i])    
    gamma.g = as.numeric(gamma.list[1])
    r = gamma.list[2]
    if(r==1){
      acc.gamma[i] = acc.gamma[i]+1
    }
    sig.array[,i,g] = sig.g
    gamma.array[,i,g] = gamma.g
  }
  ###Sample Upsilon
  XB = rep(0,nct)
  for(i in 1:p){
    XB = XB + mat.list[[i]]%*%beta.tilde[,i]
  }
  eta.star = as.vector(XB + G.Mat%*%as.vector(xi.g))
  Sig.upsilon = solve(t(U)%*%w.g.D%*%U + 1/upsilon.s*diag(Q))
  Sig.upsilon = (1/2)*(Sig.upsilon + t(Sig.upsilon))
  Mn.Upsilon = Sig.upsilon%*%(-1*t(U)%*%w.g.D%*%eta.star + t(U)%*%H)
  upsilon.g = as.vector(mvrnorm(1,Mn.Upsilon,Sig.upsilon))
  upsilon.array[1,,g] = upsilon.g
  ###Sample xi, tau, and gamma for t = 1
  eta.star = as.vector(XB)
  eta.star = as.vector(eta.star + U%*%upsilon.g)
  c1 = omega.g*(1 + zeta.g^2)/tau.g
  v4 = zeta.g/tau.g*D.diag
  c5 = zeta.g*omega.g/tau.g
  for(i in 1:t){
    w.g.t = t(G.mat.list[[i]])%*%w.g[ind.list[[i]]]
    eta.star.t = t(G.mat.list[[i]])%*%eta.star[ind.list[[i]]]
    H.t = t(G.mat.list[[i]])%*%H[ind.list[[i]]]
    sig.xi.t = 1/(w.g.t + D.diag*(1 + zeta.g^2)/tau.g)
    ###1st ID Group
    id.gr = id.grp1
    if(i==t){
      mv1 = omega.g/tau.g*W[id.gr,]%*%xi.g[,i]
    }else{
      mv1 = c1*W[id.gr,]%*%xi.g[,i]
    }
    mv2 = -1*w.g.t[id.gr]*eta.star.t[id.gr]
    mv3 = H.t[id.gr]
    if(i==1){
      mv4 = v4[id.gr]*xi.g[id.gr,(i+1)]
      mv5 = -1*c5*W[id.gr,]%*%xi.g[,(i+1)]
    }else if(i==t){
      mv4 = zeta.g/tau.g*D.diag[id.gr]*xi.g[id.gr,(i-1)]
      mv5 = -1*omega.g*zeta.g/tau.g*W[id.gr,]%*%xi.g[,(i-1)]
    }else{
      mv4 = v4[id.gr]*(xi.g[id.gr,(i-1)] + xi.g[id.gr,(i+1)])
      mv5 = -1*c5*W[id.gr,]%*%(xi.g[,(i-1)] + xi.g[,(i+1)])
    }
    mv = sig.xi.t[id.gr]*(mv1 + mv2 + mv3 + mv4 + mv5)
    xi.g[id.gr,i] = rnorm(length(id.gr),as.vector(mv),sqrt(sig.xi.t[id.gr]))
    ###2nd ID Group
    id.gr = id.grp2
    if(i==t){
      mv1 = omega.g/tau.g*W[id.gr,]%*%xi.g[,i]
    }else{
      mv1 = c1*W[id.gr,]%*%xi.g[,i]
    }
    mv2 = -1*w.g.t[id.gr]*eta.star.t[id.gr]
    mv3 = H.t[id.gr]
    if(i==1){
      mv4 = v4[id.gr]*xi.g[id.gr,(i+1)]
      mv5 = -1*c5*W[id.gr,]%*%xi.g[,(i+1)]
    }else if(i==t){
      mv4 = zeta.g/tau.g*D.diag[id.gr]*xi.g[id.gr,(i-1)]
      mv5 = -1*omega.g*zeta.g/tau.g*W[id.gr,]%*%xi.g[,(i-1)]
    }else{
      mv4 = v4[id.gr]*(xi.g[id.gr,(i-1)] + xi.g[id.gr,(i+1)])
      mv5 = -1*c5*W[id.gr,]%*%(xi.g[,(i-1)] + xi.g[,(i+1)])
    }
    mv = sig.xi.t[id.gr]*(mv1 + mv2 + mv3 + mv4 + mv5)
    xi.g[id.gr,i] = rnorm(length(id.gr),as.vector(mv),sqrt(sig.xi.t[id.gr]))
    ###3rd ID Group
    id.gr = id.grp3
    if(i==t){
      mv1 = omega.g/tau.g*W[id.gr,]%*%xi.g[,i]
    }else{
      mv1 = c1*W[id.gr,]%*%xi.g[,i]
    }
    mv2 = -1*w.g.t[id.gr]*eta.star.t[id.gr]
    mv3 = H.t[id.gr]
    if(i==1){
      mv4 = v4[id.gr]*xi.g[id.gr,(i+1)]
      mv5 = -1*c5*W[id.gr,]%*%xi.g[,(i+1)]
    }else if(i==t){
      mv4 = zeta.g/tau.g*D.diag[id.gr]*xi.g[id.gr,(i-1)]
      mv5 = -1*omega.g*zeta.g/tau.g*W[id.gr,]%*%xi.g[,(i-1)]
    }else{
      mv4 = v4[id.gr]*(xi.g[id.gr,(i-1)] + xi.g[id.gr,(i+1)])
      mv5 = -1*c5*W[id.gr,]%*%(xi.g[,(i-1)] + xi.g[,(i+1)])
    }
    mv = sig.xi.t[id.gr]*(mv1 + mv2 + mv3 + mv4 + mv5)
    xi.g[id.gr,i] = rnorm(length(id.gr),as.vector(mv),sqrt(sig.xi.t[id.gr]))
    ###4th ID Group
    id.gr = id.grp4
    if(i==t){
      mv1 = omega.g/tau.g*W[id.gr,]%*%xi.g[,i]
    }else{
      mv1 = c1*W[id.gr,]%*%xi.g[,i]
    }
    mv2 = -1*w.g.t[id.gr]*eta.star.t[id.gr]
    mv3 = H.t[id.gr]
    if(i==1){
      mv4 = v4[id.gr]*xi.g[id.gr,(i+1)]
      mv5 = -1*c5*W[id.gr,]%*%xi.g[,(i+1)]
    }else if(i==t){
      mv4 = zeta.g/tau.g*D.diag[id.gr]*xi.g[id.gr,(i-1)]
      mv5 = -1*omega.g*zeta.g/tau.g*W[id.gr,]%*%xi.g[,(i-1)]
    }else{
      mv4 = v4[id.gr]*(xi.g[id.gr,(i-1)] + xi.g[id.gr,(i+1)])
      mv5 = -1*c5*W[id.gr,]%*%(xi.g[,(i-1)] + xi.g[,(i+1)])
    }
    mv = sig.xi.t[id.gr]*(mv1 + mv2 + mv3 + mv4 + mv5)
    xi.g[id.gr,i] = rnorm(length(id.gr),as.vector(mv),sqrt(sig.xi.t[id.gr]))
    ###5th ID Group
    id.gr = id.grp5
    if(i==t){
      mv1 = omega.g/tau.g*W[id.gr,]%*%xi.g[,i]
    }else{
      mv1 = c1*W[id.gr,]%*%xi.g[,i]
    }
    mv2 = -1*w.g.t[id.gr]*eta.star.t[id.gr]
    mv3 = H.t[id.gr]
    if(i==1){
      mv4 = v4[id.gr]*xi.g[id.gr,(i+1)]
      mv5 = -1*c5*W[id.gr,]%*%xi.g[,(i+1)]
    }else if(i==t){
      mv4 = zeta.g/tau.g*D.diag[id.gr]*xi.g[id.gr,(i-1)]
      mv5 = -1*omega.g*zeta.g/tau.g*W[id.gr,]%*%xi.g[,(i-1)]
    }else{
      mv4 = v4[id.gr]*(xi.g[id.gr,(i-1)] + xi.g[id.gr,(i+1)])
      mv5 = -1*c5*W[id.gr,]%*%(xi.g[,(i-1)] + xi.g[,(i+1)])
    }
    mv = sig.xi.t[id.gr]*(mv1 + mv2 + mv3 + mv4 + mv5)
    xi.g[id.gr,i] = rnorm(length(id.gr),as.vector(mv),sqrt(sig.xi.t[id.gr]))
    ###6th ID Group
    id.gr = id.grp6
    if(i==t){
      mv1 = omega.g/tau.g*W[id.gr,]%*%xi.g[,i]
    }else{
      mv1 = c1*W[id.gr,]%*%xi.g[,i]
    }
    mv2 = -1*w.g.t[id.gr]*eta.star.t[id.gr]
    mv3 = H.t[id.gr]
    if(i==1){
      mv4 = v4[id.gr]*xi.g[id.gr,(i+1)]
      mv5 = -1*c5*W[id.gr,]%*%xi.g[,(i+1)]
    }else if(i==t){
      mv4 = zeta.g/tau.g*D.diag[id.gr]*xi.g[id.gr,(i-1)]
      mv5 = -1*omega.g*zeta.g/tau.g*W[id.gr,]%*%xi.g[,(i-1)]
    }else{
      mv4 = v4[id.gr]*(xi.g[id.gr,(i-1)] + xi.g[id.gr,(i+1)])
      mv5 = -1*c5*W[id.gr,]%*%(xi.g[,(i-1)] + xi.g[,(i+1)])
    }
    mv = sig.xi.t[id.gr]*(mv1 + mv2 + mv3 + mv4 + mv5)
    xi.g[id.gr,i] = rnorm(length(id.gr),as.vector(mv),sqrt(sig.xi.t[id.gr]))
    ###7th ID Group
    id.gr = id.grp7
    if(i==t){
      mv1 = omega.g/tau.g*W[id.gr,]%*%xi.g[,i]
    }else{
      mv1 = c1*W[id.gr,]%*%xi.g[,i]
    }
    mv2 = -1*w.g.t[id.gr]*eta.star.t[id.gr]
    mv3 = H.t[id.gr]
    if(i==1){
      mv4 = v4[id.gr]*xi.g[id.gr,(i+1)]
      mv5 = -1*c5*W[id.gr,]%*%xi.g[,(i+1)]
    }else if(i==t){
      mv4 = zeta.g/tau.g*D.diag[id.gr]*xi.g[id.gr,(i-1)]
      mv5 = -1*omega.g*zeta.g/tau.g*W[id.gr,]%*%xi.g[,(i-1)]
    }else{
      mv4 = v4[id.gr]*(xi.g[id.gr,(i-1)] + xi.g[id.gr,(i+1)])
      mv5 = -1*c5*W[id.gr,]%*%(xi.g[,(i-1)] + xi.g[,(i+1)])
    }
    mv = sig.xi.t[id.gr]*(mv1 + mv2 + mv3 + mv4 + mv5)
    xi.g[id.gr,i] = rnorm(length(id.gr),as.vector(mv),sqrt(sig.xi.t[id.gr]))
  }
  xi.g = xi.g - mean(xi.g)
  if(g%%g.save ==0){
   xi.array[,,g.s] = xi.g
   g.s = g.s + 1
  }
  B = D - omega.g*W
  tau.beta = xi.g[,1]%*%B%*%xi.g[,1]
  for(b in 2:t){
    tau.beta = tau.beta + t(xi.g[,b]- zeta.g*xi.g[,b-1])%*%B%*%(xi.g[,b]- zeta.g*xi.g[,b-1])
  }
  tau.g = rinvgamma(1,t*S/2 + a_tau,as.numeric(1/2*tau.beta+b_tau))
  A = (1/tau.g)*(D - omega.g*W)
  ###Sample Zeta
  zeta.sig = 1/zeta.s
  zeta.mean = zeta.m/zeta.s
  for(b in 2:t){
    zeta.mean = zeta.mean + xi.g[,(b-1)]%*%A%*%xi.g[,b]
    zeta.sig = zeta.sig + xi.g[,(b-1)]%*%A%*%xi.g[,(b-1)]
  }
  zeta.sig = 1/zeta.sig
  zeta.mean = zeta.sig*zeta.mean
  zeta.g = rtruncnorm(1, mean = as.numeric(zeta.mean), sd = as.numeric(sqrt(zeta.sig)),a = -1, b = 1)
  omega.list = omega.samp(omega.g,omega.var,tau.g,D,W,xi.g,zeta.g,A,t,evals)
  omega.g = omega.list[1]
  r = omega.list[2]
  if(r==1){
    acc.omega = acc.omega +1
  }
  A = 1/tau.g * (D - omega.g*W)
  tau.array[1,1,g] = tau.g
  omega.array[1,1,g] = omega.g
  zeta.array[,1,g]= zeta.g
  print(g)
  if(g%%100 == 2){
    plot(beta.array[1,1,1:g])
    plot(beta.array[5,1,1:g])
    plot(beta.array[10,1,1:g])
    plot(upsilon.array[1,1,1:g])
    plot(xi.array[1,1,1:(g.s-1)])
    plot(xi.array[10,10,1:(g.s-1)])
    plot(xi.array[1000,20,1:(g.s-1)])
    plot(gamma.array[1,1,1:g])
    plot(sig.array[1,1,1:g])
    plot(tau.array[1,1,1:g])
    plot(omega.array[1,1,1:g])
    plot(zeta.array[1,1,1:g])
    if(g<=burn){
      for(i in 1:p){
        if(acc.gamma[i]/100<=0.05){
          g.var[i] = max(0.001, g.var[i]*.9)
        }
        if(acc.gamma[i]/100>=0.5){
          g.var[i] = g.var[i]*1.1
        }
      }
      if(acc.omega/100<=0.05){
        omega.var = max(0.001, omega.var*.9)
      }
      if(acc.omega/100>=0.35){
        omega.var = omega.var*1.3
      }
      acc.gamma = rep(0,p)
      acc.omega = 0
    }
  }
}
stop.time = Sys.time()

beta.tilde.hat = apply(beta.tilde.array[,1,burn:G],1,mean)
beta.tilde.lower = apply(beta.tilde.array[,1,burn:G],1,quantile,prob = 0.025)
beta.tilde.upper = apply(beta.tilde.array[,1,burn:G],1,quantile,prob = 0.975)
beta.tilde.sd = apply(beta.tilde.array[,1,burn:G],1,sd)
res.mat = data.frame(cbind(ref.counties$FIPS, beta.tilde.hat,beta.tilde.lower,beta.tilde.upper,NA,beta.tilde.sd))
names(res.mat) <- c("FIPS","Mean","Lower0.025","Upper0.975","Significance95","StDev")
ind = beta.tilde.upper <0
res.mat$Significance[ind] = -1
ind = beta.tilde.lower <= 0 & beta.tilde.upper >= 0
res.mat$Significance[ind] = 0
ind = beta.tilde.lower > 0
res.mat$Significance[ind] = 1


ss = (G-burn)/g.save
eta.lm = matrix(99,S,ss)
t.vals = seq(1,t)/t
for(i in 1:ss){
  g.beta = 5*i + burn
  g.xi = i + burn/5
  for(s in 1:S){
    eta.vec = upsilon.array[1,1,g.beta] + beta.tilde.array[s,1,g.beta]*t.vals + xi.array[s,,g.xi]
    lm.fit = lm(eta.vec~t.vals)
    eta.lm[s,i] = lm.fit$coefficients[2]
  }
  print(i)
}

final.df = data.frame(ref.counties$FIPS)
names(final.df) = "FIPS"
final.df$etamean = apply(eta.lm,1,mean)
final.df$etalower = apply(eta.lm,1,quantile,prob = 0.025)
final.df$etaupper = apply(eta.lm,1,quantile,prob = 0.975)
final.df$etasd = apply(eta.lm,1,sd)
sig = rep(0,S)
ind = final.df$etaupper <=0
sig[ind] = -1
ind = final.df$etalower >=0
sig[ind] = 1
final.df$etasig95 = sig
