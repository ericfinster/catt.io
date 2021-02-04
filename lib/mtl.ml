(*****************************************************************************)
(*                             Monad Transformers                            *)
(*****************************************************************************)

module type Typ = sig 
  type t
end

module type Functor = sig
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
end

module type Mnd = sig
  type 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val pure : 'a -> 'a m
end

module type Traverse = sig
  type 'a t
  type 'a m
  val traverse : ('a -> 'b m) -> 'a t -> 'b t m
end

module type Applicative = sig
  include Functor
  val product : 'a t -> 'b t -> ('a * 'b) t 
  val pure : 'a -> 'a t
end

module MndToApp(M: Mnd) = struct
  type 'a t = 'a M.m
  let map f m = M.bind m (fun a -> M.pure (f a))
  let product x y = M.bind x (fun a -> M.bind y (fun b -> M.pure (a,b)))
  let pure = M.pure
end

module Identity = struct
  type 'a m = 'a
  let pure x = x
  let bind m f = f m
end

(* Now this is in global scope ... *)
type ('a,'e) err =
  | Ok of 'a
  | Fail of 'e

module ErrMnd(T: Typ) = struct
  type 'a m = ('a, T.t) err

  let pure a = Ok a
  let bind m f =
    match m with
    | Ok a -> f a
    | Fail e -> Fail e

  let throw e = Fail e
  let try_with m f =
    match m with
    | Ok a -> Ok a
    | Fail e -> f e

  let (<||>) m n = try_with m (fun _ -> n)

end

module ErrT(T: Typ)(M: Mnd) = struct
  type 'a m = (('a, T.t) err) M.m

  let pure x = M.pure (Ok x)
  let bind m f =
    M.bind m (function
        | Ok x -> f x
        | Fail e -> M.pure (Fail e))

  let lift m = M.bind m (fun x -> M.pure (Ok x))

  let throw e = M.pure (Fail e)
  let try_with m f =
    M.bind m (function
        | Ok x -> M.pure (Ok x)
        | Fail e -> f e)
      
end

module ReaderT(T: Typ)(M: Mnd) = struct
  type 'a m = T.t -> 'a M.m 

  let pure x _ = M.pure x
  let bind m f e = M.bind (m e) (fun a -> f a e)

  let ask env = M.pure env 
  let lift m _ = m
    
end  

(*****************************************************************************)
(*                            Syntax Constructors                            *)
(*****************************************************************************)

module ApplicativeSyntax(A: Applicative) = struct
    let (let+) a f = A.map f a
    let (and+) x y = A.product x y
end

module MonadSyntax(M: Mnd) = struct
  let (>>=) = M.bind
  let (let+) m f = M.bind m (fun a -> M.pure (f a))
  let (and+) x y = M.bind x (fun a -> M.bind y (fun b -> M.pure (a,b)))
  let (let*) m f = M.bind m f      
end

(*****************************************************************************)
(*                                Monad API's                                *)
(*****************************************************************************)

module type MndErr = sig
  include Mnd
  type e
  val throw : e -> 'a m
  val try_with : 'a m -> (e -> 'a m) -> 'a m
end

