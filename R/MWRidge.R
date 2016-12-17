library("glmnet")

choose_X <- function(G, n) {
  if (n != nrow(G)){
    row = sort(sample(x=1:nrow(G), size = n, replace = F))
    X = G[row,]; 
  }else if(n == nrow(G)){
    X = G;
  }
  sdg = rep(0,ncol(X));
  for ( i in 1:ncol(X) ){
    g = X[,i]
    sdg[i] = sd(g, na.rm=T)
  }
  p = ncol(X);
  index_1 = (1:p)[sdg!=0]; index_0 = (1:p)[sdg==0]
  X_1 = X[, index_1]; X_0 = X[, index_0];
  result = list("X_1"=X_1, "X_0"=X_0, "index_1"=index_1, "index_0"=index_0);
  return (result);
}

get_Nk <- function(List){
  X_1 = List$X_1; index_1 = List$index_1;
  X_0 = List$X_0; index_0 = List$index_0;
  p = ncol(X_1); q = ncol(X_0);
  X = matrix(0, nrow = nrow(X_1), ncol = p + q); 
  X[, index_1] = X_1;
  if (q!=0){
    X[, index_0] = X_0;
  }
  n = ncol(X);
  Nk = rep(0, n);
  for ( i in 1:n ){
    g = X[,i]
    Nk[i] = length(g[!is.na(g)]);
  }
  return (Nk);
}

Stand_X <- function (List) {
  X_1 = List$X_1; index_1 = List$index_1;
  X_0 = List$X_0; index_0 = List$index_0;
  for ( i in 1:ncol(X_1) ){
    g = X_1[,i]; n = length(X_1[,i][!is.na(X_1[,i])]);
    X_1[,i] = sqrt(n/(n-1))*(g - mean(g, na.rm=T))/sd(g, na.rm=T)
  }  
  if (ncol(X_0)!=0){
    for ( i in 1:ncol(X_0) ){
      X_0[,i] = rep(0, length(X_0[,i]))
    } 
  }
  List$X_1 = X_1; List$X_0 = X_0;
  return (List);
}

cor_coef <- function (d, List) {
  X = List$X_1; p = ncol(X);
  W = matrix(0, nrow = d, ncol = p-d+1);
  for ( i in 1:d ){
    W[i,] = c(i:(i+p-d))
  }
  coef = NULL; V = NULL;
  for ( k in 1:p ) {  
    W_k = W[, seq(max(1, k-d+1), min(k, p-d+1), 1)];
    
    V_k = as.vector(W_k);
    V_k = V_k[V_k!=k];
    quasi = rep(0, length(V_k));
    for ( i in 1:length(quasi) ) {
      q = sum(X[,V_k[i]]*X[,k], na.rm = T)/sqrt(sum(X[,V_k[i]]*X[,V_k[i]], na.rm = T)*sum(X[,k]*X[,k], na.rm = T))
      quasi[i] = abs(q)
    }
    coef = c(coef, list(quasi))
    V = c(V, list(V_k))
  }
  result = list(coef = coef, V = V)
  return (result)
}

CDM <- function (List, Y, Nk, cc, lambda, eta, epson = 10^(-10), M = 100) {
  X_1 = List$X_1; index_1 = List$index_1;
  X_0 = List$X_0; index_0 = List$index_0;
  p = ncol(X_1); q = ncol(X_0);
  beta = rep(0,p);
  P = rep(0, p); Q = rep(0, p); S = rep(0, p);
  coef = cc$coef; V = cc$V; Nn = Nk[index_1];
  for ( k in 1:p ) {  
    quasi = coef[[k]];
    P[k] = 1/2*(1/Nn[k]*sum(na.omit(X_1[,k]^2)) + eta*sum(quasi));
  }
  err = 1; ite = 1; res = Y - X_1 %*% beta;
  while ( (err >= epson) && (ite <= M) ) {
    temp = beta;
    for ( k in 1:p ) { 
      old.beta = beta[k];
      quasi = coef[[k]];
      beta_k = abs(beta[V[[k]]]);
      res = res + old.beta*X_1[,k];
      Q[k] = -1/Nn[k] * sum(na.omit(res*X_1[,k]))
      S[k] = lambda - eta*sum(quasi*beta_k)
      beta[k] = -sign(Q[k])*(max(abs(Q[k])-S[k], 0))/(2*P[k])
      res = res - beta[k]*X_1[,k];
    }
    ite = ite + 1; 
    err = sum(abs(temp - beta)); 
  }
  result = rep(0, p+q);
  result[index_1] = beta;
  return (result);
}

CDM_qualitative <- function(List, Y, Nk, cc, lambda, eta, epson = 10^(-8), M = 100){
  X_1 = List$X_1; index_1 = List$index_1;
  X_0 = List$X_0; index_0 = List$index_0;
  X = X_1;
  y = Y;
  p = ncol(X); n = nrow(X); q = ncol(X_0);
  P = rep(0, p); Q = rep(0, p); S = rep(0, p); 
  prob = rep(0, n); wei = prob; z = prob;
  coef = cc$coef; V = cc$V; Nn = Nk[index_1];
  proby = length(Y[Y==1])/length(Y);
  beta0 = log(proby/(1-proby));
  beta1 = rep(0, p);
  err = 1; ite = 1;
  while ((err >= epson) && (ite <= M)) {
    temp = prob; 
    for (i in 1:n){
      prob[i] = 1/(1 + exp(-beta0 - sum(X[i,]*beta1)))
      wei[i] = prob[i]*(1-prob[i])
      z[i] = beta0 + sum(X[i,]*beta1) + (y[i]-prob[i])/(prob[i]*(1-prob[i]))
      if (prob[i] >= 0.99999){
        prob[i] = 1
        wei[i] = 0.00001
        z[i] = beta0 + sum(X[i,]*beta1)
      }
      if (prob[i] <= 0.00001){
        prob[i] = 0
        wei[i] = 0.00001
        z[i] = beta0 + sum(X[i,]*beta1)
      }
    }
    for ( j in 1:p ){
      quasi = coef[[j]];
      x = X[,j]
      P[j] = 1/2*(1/Nn[j]*sum(wei * x^2) + eta*sum(quasi))
    }  
    err.in = 1; ite.in = 1;
    old=beta1
    while ( (err.in >= epson) && (ite.in <= M) ) {
      beta0 = sum(wei * (z - X %*% beta1)) / sum(wei)
      temp.in = beta1;
      res = z - beta0 - X %*% beta1;
      for ( k in 1:p ) { 
        old.beta = beta1[k]
        quasi = coef[[k]];
        beta1_k = abs(beta1[V[[k]]]);
        res = res + old.beta*X[,k];
        Q[k] = -1/Nn[k] * sum(wei * (res * X[,k]))
        S[k] = lambda - eta*sum(quasi*beta1_k)
        beta1[k] = -sign(Q[k])*(max(abs(Q[k])-S[k], 0))/(2*P[k])
        res = res - beta1[k] * X[,k]
      }
      ite.in = ite.in + 1; 
      err.in = max(abs(temp.in - beta1)); 
    }
    ite = ite + 1; 
    err = max(abs(temp - prob));
  }
  result = rep(0, p+q);
  result[index_1] = beta1;
  return (c(beta0,result));
}

MWRidge <- function(X, Y, lambda, eta, phi, d, method='linear', epson = 1e-10, M = 100){
  n = nrow(X)
  List = choose_X(X, n)
  List = Stand_X(List)
  Nk = get_Nk(List)
  cc = cor_coef(d, List)
  eta = eta/(d-1)
  if (method == 'linear'){
    Y = Y - mean(Y)
    s = CDM(List, Y, Nk, cc, lambda, eta, epson, M)
    if (length(s[s!=0]) >= 1){
      X.mw = X[,s!=0]; 
      fit = glmnet(X.mw, Y, family = "gaussian", alpha = 0, lambda = phi);
      s[s!=0] = as.numeric(fit$beta)
      names(s) = paste('v', seq(1, ncol(X), 1), sep = "")
      return (s)
    }else{
      names(s) = paste('v', seq(1, ncol(X), 1), sep = "")
      return (s)
    }    
  } else if(method == 'logistic'){
    s = CDM_qualitative(List, Y, Nk, cc, lambda, eta, epson, M)
    if (length(s[-1][s[-1]!=0]) >= 1){
      s = s[-1]
      X.mw = X[,s!=0];
      fit = glmnet(X.mw, Y, family = "binomial", alpha = 0, lambda = phi);
      s[s!=0] = as.numeric(fit$beta)
      s = c(as.numeric(fit$a0), s)
      names(s) = c('s0', paste('v', seq(1, ncol(X), 1), sep = ""))
      return (s)
    }else{
      names(s) = c('s0', paste('v', seq(1, ncol(X), 1), sep = ""))
      return (s)
    }
  } else {
    print("Error: method should be linear or logistic!")
    return (NULL)
  }
}

predict <- function(X.test, X.train, Y.train, lambda, eta, phi, d, method='linear', epson = 1e-10, M = 100){
  if (method == 'linear'){
    beta.hat = MWRidge(X.train, Y.train, lambda, eta, phi, d, method='linear', epson, M)
    n = nrow(X.test)
    List = choose_X(X.test, n)
    List = Stand_X(List)
    Nk = get_Nk(List)
    cc = cor_coef(d, List)
    eta = eta/(d-1)
    Y.mean = mean(Y.train)
    predY = (List$X_1) %*% beta.hat + Y.mean
    return (predY)
  } else if (method == 'logistic'){
    beta.hat = MWRidge(X.train, Y.train, lambda, eta, phi, d, method='logistic', epson, M)
    n = nrow(X.test)
    List = choose_X(X.test, n)
    List = Stand_X(List)
    Nk = get_Nk(List)
    cc = cor_coef(d, List)
    eta = eta/(d-1)
    predY = cbind(rep(1,n),List$X_1) %*% beta.hat
    predY = (predY>0)*1
    return (predY)
  } else {
    print("Error: method should be linear or logistic!")
    return (NULL)
  }
}