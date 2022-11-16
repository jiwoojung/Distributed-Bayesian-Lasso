library(monomvn)
library(mcmc)
library(mvtnorm)
library(glmnet)
library(ggplot2)
library(MASS)
library(pscl)
library(statmod)
library(dotwhisker)
library(dplyr)
library(gridExtra)
library(reshape2)
library(ggpattern)
library(latex2exp)

{
  loss.func = function(theta, X, Y)
  {
    s2 = theta[1]
    mu = theta[2]
    beta = theta[3:(d+2)]
    
    n = nrow(X)
    result = -n/2 * log(2*pi*s2) - 1/(2*s2) * t(Y-mu*rep(1, n)-X%*%beta)%*%(Y-mu*rep(1, n)-X%*%beta)
    
    return(-result/n)
  }
  
  loss.grad = function(theta, X, Y)
  {
    s2 = theta[1]
    mu = theta[2]
    beta = theta[3:(d+2)]
    
    n = nrow(X)
    s2.res = -n/(2*s2) + 1/(2*s2^2)*t(Y-mu*rep(1, n)-X%*%beta)%*%(Y-mu*rep(1, n)-X%*%beta)
    mu.res = n/s2 * (mean(Y)-mu)
    beta.res = 1/s2 * (t(X)%*%Y - t(X)%*%X%*%beta - mu*t(X)%*%rep(1, n))
    
    result = c(s2.res, mu.res, beta.res)
    
    return(-result/n)
  }
  
  log.prior = function(lambda2, theta)
  {
    s2 = theta[1]
    mu = theta[2]
    beta = theta[3:(d+2)]
    
    r = 1
    delta = 1.78
    
    result = -(1+d/2)*log(s2)+(d/2+r-1)*log(lambda2)-delta*lambda2-sqrt(lambda2)*norm(as.matrix(beta), type="1")/sqrt(s2)
    return(result)
  }
  
  sur.loss.m1 = function(theta)
  {
    x.local = X[1:n.local,]
    y.local = Y[1:n.local]
    loss.m1.res = loss.func(theta, x.local, y.local) - (theta)%*%(final.local.grad - final.global.grad)
    return(loss.m1.res)
  }
  
  log.posterior = function(proposal)
  {
    lambda2 = proposal[1]
    theta = proposal[-1]
    return(-n*sur.loss.m1(theta) + log.prior(lambda2, theta))
  }
  
  proposal.dist = function(theta, scale.vec=NULL)
  {
    if (is.null(scale.vec))
      scale.vec = c(0.4, 0.01, rep(0.004, d+1))
    
    return(theta + scale.vec * t(rmvnorm(1, mean = rep(0, length(theta)))))
  }
  
  # CSL Bayesian Lasso
  MCMC = function(num.iter, init.theta, scale.vec=NULL, verb=1)
  {
    chain = matrix(nrow=num.iter, ncol=d+3)
    chain[1,] = init.theta
    curr.log.posterior = log.posterior(chain[1,])
    new.log.posterior = NULL
    for (i in 1:(num.iter-1))
    {
      proposal = as.vector(proposal.dist(chain[i,], scale.vec))
      if (proposal[1] <= 0 | proposal[2] <= 0)
      {
        acceptance.prob = 0
      } else {
        new.log.posterior = log.posterior(proposal)
        acceptance.prob = exp(new.log.posterior - curr.log.posterior)
      }
      
      if (runif(1) < acceptance.prob) {
        chain[i+1,] = proposal 
        curr.log.posterior = new.log.posterior
      } else {
        chain[i+1,] = chain[i,]
      }
      if ((verb == 1) & (i%%1000 == 0))
      {
        print(i)
      }
    }
    return(chain)
  }
  
  full.log.posterior = function(theta)
  {
    X.func = X[1:n.local,]
    Y.func = Y[1:n.local]
    
    lambda2 = theta[1]
    s2 = theta[2]
    mu = theta[3]
    beta = theta[4:(d+3)]
    
    if (s2 <= 0 | lambda2 <= 0) return(-Inf)
    
    r = 1
    delta = 1.78
    
    log.post = - (n+d+2)/2 * log(s2) - 1/(2*s2) * sum((Y.func - mu - X.func%*%beta)^2) - sqrt(lambda2)*norm(as.matrix(beta), type="1")/sqrt(s2) + (d/2 + r-1)*log(lambda2) - delta*lambda2
    return(log.post)
  }
  
  log.lik = function(X, Y, theta)
  {
    s2 = theta[1]
    mu = theta[2]
    beta = theta[3:(d+2)]
    
    n = nrow(X)
    result = -n/2 * log(2*pi*s2) - 1/(2*s2) * norm(Y - mu*rep(1, n) - X%*%beta, type="2")^2
    
    return(result)
  }
  
  log.prior.consensus = function(theta)
  {
    return(log.prior(theta[1], theta[-1]))
  }
  
  log.lik.machine = function(theta, j, alpha)
  {
    x.local = X[(n.local*(j-1) + 1) : (n.local*(j-1) + alpha*n.local),]
    y.local = Y[(n.local*(j-1) + 1) : (n.local*(j-1) + alpha*n.local)]
    log.likelihood.machine = log.lik(x.local, y.local, theta[-1]) 
    return(log.likelihood.machine)
  }
  
  log.posterior.consensus = function(theta, j, alpha)
  {
    return(log.lik.machine(theta, j, alpha) + log.prior.consensus(theta)/K)
  }
  
  proposal.dist.consensus = function(theta, scale.vec=NULL)
  {
    if (is.null(scale.vec))
      scale.vec = c(1, 0.1, rep(0.05, d+1))
    return(theta + scale.vec * t(rmvnorm(1, mean = rep(0, length(theta)))))
  }
  
  # j is for the machine/sample to be used
  MCMC.consensus = function(num.iter, j, scale.vec=NULL, alpha=1, full=FALSE)
  {
    chain = matrix(nrow=num.iter, ncol=d+3)
    chain[1,] = rep(1, d+3)
    curr.log.posterior = log.posterior.consensus(chain[1,], j, alpha)
    new.log.posterior = NULL
    for (i in 1:(num.iter-1))
    {
      proposal = as.vector(proposal.dist.consensus(chain[i,], scale.vec))
      if (proposal[1] <= 0 | proposal[2] <= 0){
        acceptance.prob = 0
      } else {
        if (full) {
          acceptance.prob = exp(log.posterior.full(proposal) - log.posterior.full(chain[i,]))
        } else {
          new.log.posterior = log.posterior.consensus(proposal, j, alpha)
          acceptance.prob = exp(new.log.posterior - curr.log.posterior)
        }
      }
      
      if (runif(1) < acceptance.prob) {
        chain[i+1,] = proposal 
        curr.log.posterior = new.log.posterior
      } else {
        chain[i+1,] = chain[i,]
      }
    }
    return(chain)
  }
  
  # CMC Bayesian Lasso
  consensus.MCMC = function(num.iter, burn.in, scale.vec=NULL, alpha=1, weight="id", verb=0)
  {
    # Run MCMC on all machines
    chain = list()
    for (j in 1:K)
    {
      if (verb==1)
        print(c("Machine", j))
      chain[[j]] = MCMC.consensus(num.iter, j, scale.vec=scale.vec, alpha=alpha)
      acceptance = 1-mean(duplicated(chain[[j]][-(1:burn.in),]))
      if (verb == 1)
        print(acceptance)
    }
    
    # Calculate weighted average of draws across machines
    avg.chain = matrix(nrow=num.iter, ncol=d+3)
    chain.weights = list()
    sum.chain.weights = matrix(rep(0, (d+3)^2), nrow=d+3, ncol=d+3)
    for (j in 1:K)
    {
      if (weight=="id"){
        chain.weights[[j]] = diag(rep(1,d+3))
      } else {
        chain.weights[[j]] = solve(var(chain[[j]]))
      }
      sum.chain.weights = sum.chain.weights + chain.weights[[j]]
    }
    
    for (i in 1:num.iter)
    {
      weighted.sum = 0
      for (j in 1:K)
      {
        weighted.sum = weighted.sum + chain.weights[[j]]%*%chain[[j]][i,]
      }
      avg.chain[i,] = solve(sum.chain.weights)%*%weighted.sum
    }
    return(avg.chain)
  }
}

data(diabetes)
init.seednum = 12346
total.iter = 50

set.seed(init.seednum+1)
curr.see = NULL

X = diabetes$x
Y = diabetes$y

n = nrow(X)
d = ncol(X)
K = 13
n.local = n/K

set.seed(init.seednum+9)
order = sample(n)
X = X[order,]
Y = Y[order]

X.test = X[(n.local*10+1):n,]
Y.test = Y[(n.local*10+1):n]

X = X[1:(n.local*10),]
Y = Y[1:(n.local*10)]

n = nrow(X)
K = 10

mat.res = matrix(nrow=5, ncol=d)

## GLMNET

cvfit = cv.glmnet(X, Y)
mat.res[1,] = coef(cvfit, s="lambda.min")[-1]
mat.res[2,] = coef(cvfit)[-1]

## BLASSO

num.iter = 100000
burn.in = 10001

diab.blasso = blasso(X, Y, T=num.iter, rd=c(1,1.78), RJ=FALSE, verb=0)

blasso.res = NULL
for (i in 1:d)
{
  blasso.res = c(blasso.res, mean(diab.blasso$beta[burn.in:num.iter, i]))
}
mat.res[3,] = blasso.res

## CSL

m1.blasso = blasso(X[1:n.local,], Y[1:n.local], T=num.iter, rd=c(1,1.78), RJ=FALSE, verb=0)
m1.res = NULL
for (i in 1:d)
{
  m1.res = c(m1.res, mean(m1.blasso$beta[burn.in:num.iter, i]))
}

log.posterior.lambda = function(theta)
{
  return(log.posterior(c(mean(m1.blasso$lambda2[burn.in:num.iter]), theta)))
}

local.grad = matrix(nrow=K, ncol=d+2)
final.theta = c(mean(m1.blasso$s2[burn.in:num.iter]), mean(m1.blasso$mu[burn.in:num.iter]), m1.res)

for(i in 1:32)
{
  for (j in 1:K)
  {
    x.local = X[(n.local*(j-1) + 1) : (n.local*j),]
    y.local = Y[(n.local*(j-1) + 1) : (n.local*j)]
    local.grad[j,] = loss.grad(final.theta, x.local, y.local) 
  }
  final.local.grad = local.grad[1,]
  final.global.grad = (1/K) * colSums(local.grad)
  final.theta = optim(final.theta, log.posterior.lambda,
                      control=list(fnscale=-1))$par
}

final.local.grad = local.grad[1,]
final.global.grad = (1/K) * colSums(local.grad)

final.theta

scale.vec = c(0.1, 60, 14, 160, 200, 200, 200, 300, 300, 200, 300, 200, 200)*0.1
init.theta = c(mean(m1.blasso$lambda2[burn.in:num.iter]), final.theta)
chain = MCMC(num.iter, init.theta, scale.vec=scale.vec, verb=0)

csl.res = NULL
for (i in 4:(d+3))
{
  csl.res = c(csl.res, mean(chain[burn.in:num.iter, i]))
}
mat.res[4,] = csl.res


## CMC

scale.vec = c(0.1, 600, 10, 160, 150, 150, 150, 400, 400, 300, 300, 200, 200)*0.8
consensus.chain = consensus.MCMC(num.iter, burn.in, scale.vec=scale.vec, weight="W", verb=0)

cmc.res = NULL
for (i in 4:(d+3))
{
  cmc.res = c(cmc.res, mean(consensus.chain[burn.in:num.iter, i]))
}
mat.res[5,] = cmc.res
  

mat.res

Y.test.tilde = Y.test - mean(Y.test)
Y.test.hat = X.test%*%t(mat.res)

diabetes.res = NULL
for (i in 1:5)
{
  diabetes.res = c(diabetes.res, 1/length(Y.test) * sum((Y.test.tilde - Y.test.hat[,i])^2))
}
diabetes.res

pred.names = colnames(X)
df=data.frame(row.names=NULL)
for (i in 1:10)
{
  df.new = data.frame(row.names=NULL,
                      term=pred.names[i], 
                      estimate=coef(cvfit, s="lambda.min")[i+1], 
                      conf.low=coef(cvfit, s="lambda.min")[i+1], 
                      conf.high=coef(cvfit, s="lambda.min")[i+1], 
                      model="Lasso min")
  df = rbind(df, df.new)
  df.new = data.frame(row.names=NULL,
                      term=pred.names[i], 
                      estimate=coef(cvfit)[i+1], 
                      conf.low=coef(cvfit)[i+1], 
                      conf.high=coef(cvfit)[i+1], 
                      model="Lasso lse")
  df = rbind(df, df.new)
  chain.curr = sort(diab.blasso$beta[burn.in:num.iter, i])
  df.new = data.frame(row.names=NULL,
                      term=pred.names[i], 
                      estimate=blasso.res[i], 
                      conf.low=chain.curr[0.025*length(chain.curr)], 
                      conf.high=chain.curr[0.975*length(chain.curr)], 
                      model="Full BLasso")  
  df = rbind(df, df.new)
  chain.curr = sort(chain[burn.in:num.iter, i+3])
  df.new = data.frame(row.names=NULL,
                      term=pred.names[i], 
                      estimate=csl.res[i], 
                      conf.low=chain.curr[0.025*length(chain.curr)], 
                      conf.high=chain.curr[0.975*length(chain.curr)], 
                      model="CSL BLasso")  
  df = rbind(df, df.new)
  chain.curr = sort(consensus.chain[burn.in:num.iter, i+3])
  df.new = data.frame(row.names=NULL,
                      term=pred.names[i], 
                      estimate=cmc.res[i], 
                      conf.low=chain.curr[0.025*length(chain.curr)], 
                      conf.high=chain.curr[0.975*length(chain.curr)], 
                      model="CMC BLasso")  
  df = rbind(df, df.new)
}

dwplot(df, dodge_size=0.6, dot_args=list(size=3), whisker_args=list(size=1),
       vline = geom_vline(xintercept=0, colour="grey50", linetype="dashed")) +
  theme(legend.title=element_blank(),
        legend.position=c(0.1, 0.1)) +
  labs(title="Lasso Estimates and Intervals for Diabetes Data", x="Standardised coefficients", y="Variables")

post.plots = list()
for (i in 1:10)
{
  df = data.frame(
    Full = diab.blasso$beta[burn.in:num.iter,i],
    CSL = chain[burn.in:num.iter,i+3],
    CMC = consensus.chain[burn.in:num.iter,i+3]
  )
  
  mdf = melt(df)
  names(mdf)[1] = "Method"
  
  curr.plot = ggplot(mdf, aes(x=value, group=Method, colour=Method, fill=Method, linetype=Method)) +
    labs(title=paste("Marginal Posterior Distribution of", colnames(X)[i]), x="", y="") +
    geom_density(alpha=0.3) +
    theme(legend.position = c(0.11,0.6))
  
  post.plots[[i]] = curr.plot
}

grid.arrange(post.plots[[1]],post.plots[[2]],post.plots[[3]],post.plots[[4]],
             post.plots[[5]],post.plots[[6]],post.plots[[7]],post.plots[[8]],
             post.plots[[9]],post.plots[[10]],
             ncol=2, nrow=5)

