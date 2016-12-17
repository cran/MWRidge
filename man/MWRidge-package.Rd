\name{MWRidge}
\alias{MWRidge}
\alias{predict}
\title{
Two Stage Moving-Window Ridge Method for Prediction and Estimation
}
\author{
Minli Bao <minli-bao@uiowa.edu>
}

\description{
Find coefficients for a penalized regression model. Moving-window penalty is applied in the first stage and ridge regression is applied in the second stage.
}

\usage{
MWRidge(X, Y, lambda, eta, phi, d, method='linear', epson = 1e-10, M = 100)
predict(X.test, X.train, Y.train, lambda, eta, phi, d, method='linear', 
        epson = 1e-10, M = 100)
}

\arguments{
\item{X}{The design matrix.}
\item{Y}{The response variable.}
\item{lambda}{The L1 penalty tuning parameter.}
\item{eta}{The moving-window penalty tuning parameter.}
\item{phi}{The L2 penalty tuning parameter.}
\item{d}{The size of the moving-window penalty.}
\item{method}{The regression method. Method can be linear or logistic.}
\item{X.test}{The design matrix for the test data.}
\item{X.train}{The design matrix for the training data.}
\item{Y.train}{The response variable for the training data.}
\item{epson}{Convergence criterion. The iteration will stop if the relative change is smaller than epson.}
\item{M}{The maximum number of iterations.}
}

\details{
There is a two-stage regularized regression method. In the first stage, the function minimizes 1/(2n)*SSE + lambda*L1 + eta/(2(d-1))*MW. Here SSE is the sum of squared error, L1 is the L1 penalty in Lasso and MW is the moving-window penalty. In the second stage, the function minimizes 1/(2n)*SSE + phi/2*L2. Here L2 is the L2 penalty in ridge regression.
}
\value{
MWRidge returns:
\item{beta}{The coefficients estimates.}
predict returns:
\item{y.hat}{The prediction of the test data based on the model trained on the training data.}
}

\keyword{ model fitting }

\examples{
n = 100
p = 200
set.seed(1)
X = matrix(rnorm(n * p, mean = 0, sd = 1), nrow = n, ncol = p)
beta = runif(p)
err = rnorm(n)
Y = X \%*\% beta + err
beta.hat = MWRidge(X, Y, lambda = 1, eta = 2, phi = 1, d = 2, method = 'linear')

prob = exp(X \%*\% beta)/(1 + exp(X \%*\% beta))
Y = rbinom(n, 1, as.vector(prob))
beta.hat = MWRidge(X, Y, lambda = 0.1, eta = 0.2, phi = 1, d = 2, method = 'logistic')

X.test = matrix(rnorm(50 * p, mean = 0, sd = 1), nrow = 50, ncol = p)
Y.hat = predict(X.test, X, Y, lambda = 0.1, eta = 0.2, phi = 1, d = 2, method = 'logistic')
}