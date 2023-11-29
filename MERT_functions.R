suppressMessages( library(dplyr) ) # Manipulações de funções
suppressMessages( library(mvtnorm) ) # Manipulações de funções
suppressMessages( library(tidyr) ) # Manipulações de funções

# Regression trees
suppressMessages( library(rpart) )

# Pacotes para a construção de gráficos
suppressMessages( library(ggplot2) )
suppressMessages( library(cowplot) )
suppressMessages( library(latex2exp) )
suppressMessages( library(GGally) )

generate_subject <- function(Xi, beta, Zi, D, sigma2, random_state = NULL){
    # Only if requested a non NULL seed
    if(!is.null(random_state)){
        # Save the current global random state so that the randomness inside the function doesn't affect the overall randomness
        old_random_state <- get0(".Random.seed", envir = .GlobalEnv, inherits = FALSE)
        set.seed(random_state)
    }
    
    ni <- nrow(Xi) # Number of observations from the subject
    p <- ncol(Xi) # Numer of fixed effects
    q <- ncol(Zi) # Numer of random effects
    
    # Generate the random effects vector for this subject
    # If q is NULL or q = 1, we have only one column in Zi
    if(is.null(q) || q == 1 ){
        bi <- rnorm(1, mean = 0, sd = sqrt(D))
        Zi <- as.matrix(Zi)
    }else{
        bi <- rmvnorm(1, mean = rep(0, q), sigma = D ) %>% t
    }
    
    # Generate the residuals epsilon
    e <- rmvnorm(1, mean = rep(0, ni), sigma = sigma2 * diag(ni) ) %>% t
    
    if(!is.null(random_state)){
        # Returns the overall random state to the one from before the function call
        assign(".Random.seed", old_random_state, envir = .GlobalEnv, inherits = FALSE)
    }
    
    Yi <- Xi %*% beta + Zi %*% bi + e
    
    return(list(
        "Y" = as.vector(Yi),
        "random_effects" = as.vector(bi),
        "residuals" = as.vector(e)
    ))
}

# Generate multiple subjects from the usual mixed effects model
generate_sample <- function(N, Xi, beta, Zi, D, sigma2){
    # If it's given only one matrix Xi, consider all the subjects to have the same Xi
    if( all(class(Xi) != "list") ){ Xis <- rep(list(Xi), N) }else{ Xis <- Xi }
    # If it's given only one matrix Zi, consider all the subjects to have the same Zi
    if( all(class(Zi) != "list") ){ Zis <- rep(list(Zi), N) }else{ Zis <- Zi }
    
    subjects <- sapply(1:N, function(i){
        Xi <- Xis[[i]]
        Zi <- Zis[[i]]
        
        subject <- generate_subject(Xi, beta, Zi, D, sigma2)
        subject
    }) %>% t %>% as.data.frame
    
    # Matrix with all the random effects from each subject
    random_effects <- Reduce(rbind, subjects$random_effects)
    # Matrix with all the residuals from every subject
    residuals <- Reduce(rbind, subjects$residuals)
    
    rownames(random_effects) <- rep("", nrow(random_effects))
    rownames(residuals) <- rep("", nrow(residuals))
    
    # Column names of all the variables
    col_names <- colnames(Xis[[1]])
    # In order to build complete dataset, first removes the intercepts columns from all the matrices
    Xis <- lapply(Xis, function(Xi){
        if( all(Xi[,1] == 1) ){ Xi <- Xi[,-1] }
        # If objects turns out to be of class numeric (single column), convert it to vector matrix
        if( all(class(Xi) == "numeric") ){
            Xi <- as.matrix(Xi)
            colnames(Xi) <- col_names[2]
        }
        Xi
    })
    
    # data.frame with subjects' responses as list type column
    Y <- tibble(response = subjects$Y )
    
    # Each remaining column of the Xi and Zi matrices are then transformed to grouped variables in a data.frame
    covariates <- sapply(Xis, function(Xi){
        # Each columns of the design matrix is a column of the dataset
        new_columns <- list()
        for(i in 1:ncol(Xi)){
            new_columns[[i]] <- Xi[,i]
        }
        
        # Adds a column of zeros just to guarantee that sapply is returning a matrix and not a vector
        c(new_columns, 0)
    }) %>% t %>% as.data.frame
    
    # Final generated dataset
    data <- cbind(
        1:nrow(Y),
        Y,
        covariates
    )
    
    # Removes the zero column added previously
    data <- data[,-ncol(data)]
    colnames(data) <- c("id", "Y", colnames(Xis[[1]]))
    
    # Unnest all columns
    data <- data %>% unnest(cols = colnames(data)[-1])
    
    return(list(
        "Xis" = Xis,
        "Zis" = Zis,
        "covariates" = covariates,
        "data" = data,
        "Y" = Y,
        "bi" = random_effects,
        "epsiloni" = residuals
    ))
}

train_MERT <- function(df, fixed_effects_form, Ys, Xis, Zis, e, response_name, verbose = TRUE, max_iter = 200){    
    N <- length(Xis)
    count <- 0
    q <- ncol(Zis[[1]])
    
    # ------------------ Step 0 ------------------
    r <- 0
    bi_hat <- rep(list(matrix(rep(0, q))), N)
    sigma2_hat <- 1
    D_hat <- diag(q)
    
    # Stop criterion
    GLLs <- c(0)
    
    converged <- FALSE
    while(!converged){
        
        r <- r + 1
        
        # ------------------ Step 1 ------------------
        
        # Recover the vectors Yi* for all subjects and join them in a single big vector
        
        # ------------------ (i)
        Y_star <- lapply(1:N, function(i){
            Yi <- Ys[[i]]
            Zi <- Zis[[i]]
            bi <- bi_hat[[i]]
            
            Yi - Zi %*% bi
        })
        Y_star <- Reduce(rbind, Y_star)
        
        df_star <- df
        df_star$Y <- Y_star[,1]
        
        # ------------------ (ii)
        # Fit and obtain the f_hat values for all individuals
        fit_rpart <- rpart(fixed_effects_form, data = df_star)
        f_y_hat <- predict(fit_rpart)
        
        # Once predicted by the rpart, segment the responses by subject again
        df_star <- cbind(df_star, f_y_hat)
        
        # return(df_star)
        
        # Format the predicted responses on the subject wise form
        f_y_hat <- (df_star %>% group_by(id) %>% summarise(f_y_hat = list(f_y_hat)))$f_y_hat
        
        # return(f_y_hat)
        
        # ------------------ (iii)
        Vi_hat <- list()
        Vi_hat_inv <- list()
        for(i in 1:N){
            Yi <- Ys[[i]]
            f_hat <- f_y_hat[[i]]
            
            Zi <- Zis[[i]]
            ni <- nrow(Zi)
            
            # Update estimate the covariances matrix of the response variable
            Vi <- Zi %*% D_hat %*% t(Zi) + sigma2_hat * diag(ni)
            Vi_hat[[i]] <- Vi
            # Obtain the inverses of the matrices Vi for further calculations
            Vi_inv <- solve(Vi)
            Vi_hat_inv[[i]] <- Vi_inv
            
            # Update estimate the random effects
            bi_hat[[i]] <- D_hat %*% t(Zi) %*% Vi_inv %*% (Yi - f_hat)
        }
        
        # ------------------ Step 2 ------------------
        
        sigma2_hat <- (lapply(1:N, function(i){
            Yi <- Ys[[i]]
            f_hat <- f_y_hat[[i]]
            
            Zi <- Zis[[i]]
            ni <- nrow(Zi)
            
            Vi_inv <- Vi_hat_inv[[i]]
            bi <- bi_hat[[i]]
            
            # Update estimate the residual error epsilon
            epsilon_i <- Yi - f_hat - Zi %*% bi
            
            # Update estimate of sigma2
            t(epsilon_i) %*% epsilon_i + sigma2_hat * (ni - sigma2_hat*sum(diag(Vi_inv)))
        }) %>% unlist %>% sum) / nrow(df)
        
        D_hat <- lapply(1:N, function(i){
            Yi <- Ys[[i]]
            Zi <- Zis[[i]]
            ni <- nrow(Zi)
            
            bi <- bi_hat[[i]]
            Vi_inv <- Vi_hat_inv[[i]]
            
            bi %*% t(bi) + D_hat - D_hat %*% t(Zi) %*% Vi_inv %*% Zi %*% D_hat
        })
        D_hat <- Reduce("+", D_hat) / N
        
        # Stop criterion (Generalized log-likelihood)
        aux_GLL <- lapply(1:N, function(i){
            Yi <- Ys[[i]]
            f_hat <- f_y_hat[[i]]
            
            Zi <- Zis[[i]]
            ni <- nrow(Zi)
            
            bi <- bi_hat[[i]]
            Vi_inv <- Vi_hat_inv[[i]]
            
            G <- Yi - f_hat - Zi%*%bi
            
            t(G) %*% G / sigma2_hat + t(bi) %*% solve(D_hat) %*% bi + log(det(D_hat)) + ni*log(sigma2_hat)
        }) %>% unlist %>% sum

        if(abs(aux_GLL - GLLs[length(GLLs)]) <= e | r >= max_iter){
            converged <- TRUE
        }else{
            GLLs[r+1] <- aux_GLL
        }            
    }
    
    if(verbose){
        cat("Converged after", r, "iterations. Difference in GLLs of", abs(GLLs[length(GLLs)] - GLLs[length(GLLs)-1]))
    }
    
    ids <- unique(df$id)
    names(bi_hat) <- ids
    
    return(list(
        "f" = fit_rpart,
        "bi" = bi_hat,
        "sigma2" = sigma2_hat,
        "D" = D_hat,
        "r" = r,
        "GLL" = GLLs[-1]
    ))
}

# Predict the response for an individual, given its matrices Xi and Zi.
# The individuals ids have to be specified in order to use the random effects. If not its assumed bi unobserved (just the population mean)
predict_MERT <- function(fit, Xis, Zis, ids = NULL){
    
    predict_single <- function(fit, Xi, Zi, id){
        Xi <- as.data.frame(Xi)
        Zi <- as.data.frame(Zi)
        
        fixed_part <- predict(fit$f, newdata = Xi)
        
        # If the subject id is not given, assume its a new individual, returning just the population mean
        if(is.null(id) | !(id %in% names(fit$bi))){
            return( fixed_part )
        }
        
        random_part <- as.matrix(Zi) %*% as.matrix(fit$bi[[as.character(id)]]) %>% as.vector
        return( fixed_part + random_part )
    }
    
    # Check if it's a single prediction or a list of predictions to be made
    if( any(class(Xis) != "list") ){
        return( predict_single(fit, Xis, Zis, ids) )
    }else{
        pred <- list()
        for(i in 1:length(Xis)){
            id <- ids[i]
            Xi <- Xis[[i]]
            Zi <- Zis[[i]]
            pred[[i]] <- predict_single(fit, Xi, Zi, id)
        }
        return(pred)
    }
}