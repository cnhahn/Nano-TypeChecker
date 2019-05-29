{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = readFile f >>= typeOfString

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseExpr s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars ttype = case ttype of 
            TInt -> []
            TBool -> []
            t1 :=> t2 -> (freeTVars t1) ++ (freeTVars t2)
            TVar ttvar -> [ttvar] 
            TList ttlist -> freeTVars ttlist      
--  freeTVars t     = error "TBD: type freeTVars"

-- need to write an if statment on stuff where we take check what t1 is and t2 is then return what they are in a correct format of freeTVars t1 and freeTvars t2...

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
   freeTVars ppoly = case ppoly of 
             Mono ttype -> freeTVars ttype
             Forall ttvar ttype ->  L.filter (\a -> (ttvar /= a)) (freeTVars ttype)
 --    Forall ttvar ttype -> freeTVars ttype L.\\ ([ttvar] ++ [ttvar]) 
                 --[a a]  t1 // [a] t2 

--  freeTVars s     = error "TBD: poly freeTVars"

--rmemeber what was bound  and delete what was in that list  (forall TVar poly delete what was in TVar)             
--search for all the cases of ttvar in ttypes and then delete when you find them.

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar key [] =  TVar key
lookupTVar key ((ttvar, ttype):gamma) 
            | key == ttvar = ttype 
            | otherwise = lookupTVar key gamma

--lookupTVar a sub =error "TBD: lookupTVar"
--lookupTVar key [] = throw (Error ("unbound variable: " ++ key))

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar key [] = throw (Error ("unbound variable: " ++ key))

removeTVar key gamma = L.filter fun gamma
          where
           fun = (\(a,b) -> (key /= a)) 

--removeTVar a sub = error "TBD: removeTVar"

-- L.filter function restoflist
-- make a function that checks a pair of a list and returns a list
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  -- apply sub t         = error "TBD: type apply"
   apply _ (TInt)         = TInt
   apply _ (TBool)        = TBool            
   apply sub (TVar ttvar) = TVar ttvar                
   apply sub (t1 :=> t2)  = (apply sub t1) :=> (apply sub t2)
   apply sub (TList tlist) = TList (apply sub tlist)
            
--lookup ttype in () return its actual type form the list, if type is already given to you dont have to look up, but if you are given A and the list then check if A is there then return its type.       
           
-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub s         = error "TBD: poly apply"

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a t = error "TBD: extendSubst"
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving Show

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st a t = error "TBD: unifyTVar"
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 = error "TBD: unify"

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
--infer st _   (EInt _)          = error "TBD: infer EInt"
--infer st _   (EBool _)         = error "TBD: infer EBool"
--infer st gamma (EVar x)        = error "TBD: infer EVar"
--infer st gamma (ELam x body)   = error "TBD: infer ELam"
--infer st gamma (EApp e1 e2)    = error "TBD: infer EApp"
--infer st gamma (ELet x e1 e2)  = error "TBD: infer ELet"
infer st _   (EInt _)          = (st, TInt)
infer st _   (EBool _)         = (st, TBool)

infer st gamma (EVar x)        = error "TBD: infer EVar" -- need gamma to be someting not as expr (st, (lookupTVar x gamma))
infer st gamma (ELam x body)   = error "TBD: infer ELam"
infer st gamma (EApp e1 e2)    = error "TBD: infer EApp"

infer st gamma (ELet x e1 e2)  = error "TBD: infer ELet"
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = error "TBD: generalize"
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = error "TBD: instantiate"
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Mono $ TBool :=> TBool :=> TBool)
  , ("!=",   Mono $ TBool :=> TBool :=> TBool)
  , ("<",    Mono $ TBool :=> TBool :=> TBool)
  , ("<=",   Mono $ TBool :=> TBool :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   error "TBD: if")
  -- lists: 
  , ("[]",   error "TBD: []")
  , (":",    error "TBD: :")
  , ("head", error "TBD: head")
  , ("tail", error "TBD: tail")
  ]
