```agda
module FSInterface where

open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Tree using (Tree; TreeList; []; _∷_; TreeShape;
    V; L′; _⇒_; get; V-∀; N; node; _∈_; here; there; status;
    get-list; self; tran; child; _+ᵖ_; get-+ᵖ; get-status;
    _∈ᶜ_; ≤ˢ-max-eq; ≡-≤ˢ; erase; erase-V; add-shape; add-V; add;
    add-≡; live; erased; Status; _≰ᵖ_; erase-other; as-↑;
    add-other; add-shape-N; _≤ᵖ_; ≤ᵖ-id; ≤ᵖ-trans)
```

## Interface as a record

```agda
record IsFS (A : Set) : Set₁ where
    -- `A` is the type of the file system
    -- The types of FSObj, IsDir and so on might depend on the file system type A
    field
        -- Basic types
        -- what is an Obj of this file system?
        FSObj : A → Set
        -- what is root?
        -- this also implicitly states that the root is unique
        root : ∀ {a} → FSObj a
        -- what is the information that an object could contain?
        Info : Set

        -- Functions & properties related to objects
        -- equality between objects
        _≡ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set 
        -- this relation should be an equivalence relation
        ≡ᵒ-trans : ∀ {a obj₂ obj₃} {obj₁ : FSObj a} → obj₁ ≡ᵒ obj₂ → obj₂ ≡ᵒ obj₃ → obj₁ ≡ᵒ obj₃
        ≡ᵒ-sym : ∀ {a obj₁} {obj₂ : FSObj a} → obj₁ ≡ᵒ obj₂ → obj₂ ≡ᵒ obj₁
    
    IsNotRoot : ∀ {a} → FSObj a → Set
    IsNotRoot obj = ¬ (obj ≡ᵒ root)

    field
        -- what is a directory? (should be decidable)
        IsDir : ∀ {a} → FSObj a → Set 
        -- also, root should be a dir
        RootIsDir : ∀ {a} → IsDir (root {a})
        -- extracting the information that an object processes
        extract : ∀ {a} → FSObj a → Info

        -- `contained` relation (should be a partial order)
        _≤ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
        -- properties that a partial order should satisfy
        ≤ᵒ-id : ∀ {a} {obj : FSObj a} → obj ≤ᵒ obj
        ≤ᵒ-trans : ∀ {a} {obj₁ : FSObj a} {obj₂ obj₃} →
            obj₁ ≤ᵒ obj₂ → obj₂ ≤ᵒ obj₃ → obj₁ ≤ᵒ obj₃ 
    
    -- Previous IsNotContained
    _≰ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
    _≰ᵒ_ obj₁ obj₂ = ¬ (obj₁ ≤ᵒ obj₂)

    field
        -- when we say an object is a child of another object?
        IsChild : ∀ {a} → FSObj a → FSObj a → Set
        -- get children of a directory, with the proof that they are indeed children
        get-children : ∀ {a} → (obj : FSObj a) → IsDir obj 
            → List (Σ[ kid ∈ (FSObj a) ] IsChild obj kid)
        -- get the parent (given that the object is not root), with the proof that it is indeed the parent
        get-parent : ∀ {a} → (obj : FSObj a) → IsNotRoot obj
            → Σ[ par ∈ (FSObj a) ] IsChild par obj

        -- Functions & properties related to file systems (A)
        -- removing an object gives another FS
        remObj : ∀ {a} → (obj : FSObj a) → IsNotRoot obj → A
        -- for the objects that aren't contained in the removed object, there is
        -- a mapping to objects of the new FS, and their information is unchanged
        --                    obj-remove           not-root           obj-original
        rem-map : ∀ {a} → (objr : FSObj a) → (nr : IsNotRoot objr) → (objo : FSObj a)
            → objr ≰ᵒ objo
            → Σ[ objn ∈ FSObj (remObj objr nr) ] extract objo ≡ extract objn
        -- adding an object gives another FS
        addFS : ∀ {a} → (obj : FSObj a) → IsDir obj → A → A
        -- for the objects that aren't contained in the directory that's being modified,
        -- there is a mapping to objects of the new FS, and their information is unchanged
        --                     obj-modify      isdir obj-modify
        add-map : ∀ {a} → (objm : FSObj a) → (idom : IsDir objm) → (b : A)
            → (objo : FSObj a) → objo ≰ᵒ objm
            → Σ[ objn ∈ FSObj (addFS objm idom b) ] extract objo ≡ extract objn
```   

Now we have an interface, it is time to implement this interface based on
the tree model we already have.

```agda
-- A file system is a tree that's (1) valid (2) with live root (3) root is a node
FS : Set
FS = Σ[ x ∈ TreeShape ] (Σ[ tx ∈ Tree x ] V tx × L′ tx × N x)

-- An Object is a live object of the tree
FSObj : FS → Set
FSObj (x , tx , vx , lx , nx) = Σ[ y ∈ TreeShape ] (Σ[ x⇒y ∈ x ⇒ y ] L′ (get x⇒y tx))

-- The root is just the root object of the tree
root : ∀ {fx} → FSObj fx
root {(x , tx , vx , lx , nx)} = x , self , lx

-- the information an object would contain is just `Status`
-- this could be easily extended to strings and so on
Info : Set
Info = Status

-- equality for paths
data _≡ᵖ_ : ∀ {x y z} → x ⇒ y → x ⇒ z → Set where
    refl : ∀ {x y} {x⇒y : x ⇒ y} → x⇒y ≡ᵖ x⇒y

≡ᵖ-trans : ∀ {x y z a} {x⇒y : x ⇒ y} {x⇒z : x ⇒ z} {x⇒a : x ⇒ a} 
    → x⇒y ≡ᵖ x⇒z → x⇒z ≡ᵖ x⇒a → x⇒y ≡ᵖ x⇒a
≡ᵖ-trans refl refl = refl

≡ᵖ-sym : ∀ {x y z} {x⇒y : x ⇒ y} {x⇒z : x ⇒ z} 
    → x⇒y ≡ᵖ x⇒z → x⇒z ≡ᵖ x⇒y
≡ᵖ-sym refl = refl

≡-≡ᵖ : ∀ {x y a} {x⇒y : x ⇒ y} {x⇒z : x ⇒ y} {x⇒a : x ⇒ a} 
    → x⇒y ≡ x⇒z → x⇒z ≡ᵖ x⇒a → x⇒y ≡ᵖ x⇒a
≡-≡ᵖ refl refl = refl

-- equality for objects, 
-- since our fs objects contain proofs now, we need an equality
-- with proof irrelavance (i.e. simply just don't care about it)
_≡ᵒ_ : ∀ {fx : FS} → FSObj fx → FSObj fx → Set
(y , x⇒y , pf) ≡ᵒ (z , x⇒z , pf′) = y ≡ z × (x⇒y ≡ᵖ x⇒z)

≡ᵒ-trans : ∀ {fx} {obj₁ obj₂ obj₃ : FSObj fx} → _≡ᵒ_ {fx} obj₁ obj₂ → _≡ᵒ_ {fx} obj₂ obj₃ 
    → _≡ᵒ_ {fx} obj₁ obj₃
≡ᵒ-trans (a=b , pa=b) (b=c , pb=c) = trans a=b b=c , ≡ᵖ-trans pa=b pb=c

≡ᵒ-sym : ∀ {fx : FS} {obj₁} {obj₂ : FSObj fx} → _≡ᵒ_ {fx} obj₁ obj₂ → _≡ᵒ_ {fx} obj₂ obj₁
≡ᵒ-sym (refl , refl) = refl , refl

isdir : ∀ {fx} → FSObj fx → Set
isdir (y , _ , _) = N y

rootisdir : ∀ {fx} → isdir {fx} (root {fx})
rootisdir {(x , _ , _ , lx , nx)} = nx

extract : ∀ {fx} → FSObj fx → Status
extract {_ , tx , _ , _} (_ , x⇒y , _) = get-status x⇒y tx 

_≤ᵒ_ : ∀ {fx} → FSObj fx → FSObj fx → Set
(_ , x⇒y , _) ≤ᵒ (_ , x⇒z , _) = x⇒y ≤ᵖ x⇒z

≤ᵒ-id : ∀ {fx} {obj : FSObj fx} → _≤ᵒ_ {fx} obj obj
≤ᵒ-id = ≤ᵖ-id

≤ᵒ-trans : ∀ {fx} {obj₁ : FSObj fx} {obj₂ obj₃} →
    _≤ᵒ_ {fx} obj₁ obj₂ → _≤ᵒ_ {fx} obj₂ obj₃ → _≤ᵒ_ {fx} obj₁ obj₃ 
≤ᵒ-trans a b = ≤ᵖ-trans a b

-- ischild
iskid : ∀ {fx} → FSObj fx → FSObj fx → Set
iskid (x , _) (y , _) = y ∈ᶜ x

get-children : ∀ {fx} → (obj : FSObj fx) → isdir {fx} obj 
    → List (Σ[ kid ∈ (FSObj fx) ] iskid {fx} obj kid)
get-children {fx@(x , tx , _)} obj@(node ys , x⇒y , pv) node = map-∈ gen-∈
    where
        ty = get x⇒y tx
        -- get the treelist associated with a node
        get-tl : ∀ {ys} → Tree (node ys) → TreeList ys
        get-tl (node _ tys) = tys
        -- generate the list of all membership relations
        gen-∈ : ∀ {ys} → List (Σ[ x ∈ TreeShape ] x ∈ ys)
        gen-∈ {[]} = []
        gen-∈ {y ∷ ys} = (y , here) ∷ map 
            (λ (x , x∈xs) → (x , there x∈xs)) (gen-∈ {ys})
        -- map the list of membership relations to children
        map-∈ : List (Σ[ x ∈ TreeShape ] x ∈ ys) 
            → List (Σ[ kid ∈ (FSObj fx) ] iskid {fx} obj kid)
        map-∈ [] = []
        map-∈ ((z , z∈ys) ∷ rest) with status (get-list z∈ys (get-tl ty)) in eq
        ... | live = ((z , x⇒y +ᵖ tran (child z∈ys) self , 
            (begin get-status (x⇒y +ᵖ tran (child z∈ys) self) tx 
            ≡⟨ cong status (get-+ᵖ x⇒y (tran (child z∈ys) self) tx) ⟩ 
            get-status (tran (child z∈ys) self) ty 
            ≡⟨ cong status (cong (get (tran (child z∈ys) self)) (guide ty)) ⟩
            eq)), child z∈ys 
            ) ∷ map-∈ rest
            where
                -- to guide the type system to see this simple fact...
                guide : ∀ {ys} → (ty : Tree (node ys)) 
                    → ty ≡ node (status ty) (get-tl ty)
                guide (node _ _) = refl
        ... | erased = map-∈ rest

-- help function for get-parent to reverse induction with proof
gp-help : ∀ {x z} → (x⇒z : x ⇒ z) → ¬ (x⇒z ≡ᵖ self) 
    → Σ[ y ∈ TreeShape ] (Σ[ x⇒y ∈ x ⇒ y ] 
        (Σ[ z∈y ∈ z ∈ᶜ y ] x⇒z ≡ x⇒y +ᵖ tran z∈y self)) 
gp-help self neg = ⊥-elim (neg refl)
gp-help {x} (tran z∈ᶜx y⇒z) neg with y⇒z in eq
... | self = x , self , z∈ᶜx , refl
... | tran _ _ = let
            ts , path , kid , pf = gp-help y⇒z λ eqp → 
                CONTRA (≡ᵖ-trans (≡ᵖ-sym (≡-≡ᵖ eq refl)) eqp)
        in ts , tran z∈ᶜx path , kid , 
            cong (tran z∈ᶜx) (trans (sym eq) pf)
        where
            CONTRA : ∀ {x y z a b} → tran {y} {x} {z} a b ≡ᵖ self → ⊥
            CONTRA ()

-- get parent
get-parent : ∀ {fx} → (obj : FSObj fx) → ¬ (_≡ᵒ_ {fx} obj (root {fx})) 
    → Σ[ par ∈ FSObj fx ] iskid {fx} par obj
get-parent (x , self , eq) neq = ⊥-elim (neq (refl , refl))
get-parent {x , tx , vx , lx} (_ , x⇒z@(tran _ _) , lz) neq = let
        y , x⇒y , z∈y , pf = gp-help x⇒z λ ()
    in
        (y , x⇒y , 
        ≤ˢ-max-eq (≡-≤ˢ (sym lz) 
        (≡-≤ˢ (cong (λ x → get-status x tx) pf) (vx x⇒y (tran z∈y self))))) , 
        z∈y

remObj : ∀ {fx} → (obj : FSObj fx) → ¬ (_≡ᵒ_ {fx} obj (root {fx})) → FS
remObj (x , self , eq) neq = ⊥-elim (neq (refl , refl))
remObj {x , tx@(node _ _) , vx , lx} (y , x⇒y@(tran (child _) _) , eq) neq = x , 
    erase x⇒y tx , erase-V x⇒y tx vx , lx

rem-map : (fx : FS) → (objr : FSObj fx) → (nr : ¬ (_≡ᵒ_ {fx} objr (root {fx})))
    → (objo : FSObj fx) → ¬ (_≤ᵒ_ {fx} objr objo)
    → Σ[ objn ∈ FSObj (remObj {fx} objr nr) ] extract {fx} objo ≡ extract {remObj objr nr} objn
rem-map (x , tx , vx , _) (x , self , eq) neq _ _ = ⊥-elim (neq (refl , refl))
rem-map (x , tx@(node _ _) , _) (y , x⇒y@(tran (child _) _) , _) nr (a , x⇒a , la) nc 
    = (a , x⇒a , trans (sym eq) la) , eq
    where
        eq = erase-other x⇒y x⇒a nc tx

addFS : ∀ {fx} → (obj : FSObj fx) → isdir {fx} obj → FS → FS
addFS {fx@(x , tx , vx , lx , nx)} (y , x⇒y , ly) node (a , fa , va , la) 
    = add-shape (rootisdir {fx}) node x⇒y a , add x⇒y tx fa , add-V x⇒y vx va ly , 
    trans (add-≡ (rootisdir {fx}) node tx fa x⇒y) lx , add-shape-N (rootisdir {fx}) node x⇒y 

add-map : ∀ {fx} → (objm : FSObj fx) → (idom : isdir {fx} objm) → (fa : FS)
    → (objo : FSObj fx) → ¬ (_≤ᵒ_ {fx} objo objm)
    → Σ[ objn ∈ FSObj (addFS {fx} objm idom fa) ] extract {fx} objo ≡ extract {addFS {fx} objm idom fa} objn
add-map {fx@(x , tx , vx , _)} (y , x⇒y , ly) node (a , fa , va , _) (b , x⇒b , lb) nc = 
    (b , as-↑ x⇒y x⇒b nc a , trans (sym eq) lb) , eq
    where
        eq = add-other {_} {_} {rootisdir {fx}} {node} x⇒y x⇒b nc tx fa ly
```

```agda
_ : IsFS FS
_ = record{ FSObj = FSObj
    ; root = root -- a lot of yellow, maybe becasue of eta-equality?
    ; Info = Info
    ; _≡ᵒ_ = _≡ᵒ_
    ; ≡ᵒ-trans = ≡ᵒ-trans
    ; ≡ᵒ-sym = ≡ᵒ-sym
    ; IsDir = isdir
    ; RootIsDir = rootisdir
    ; extract = extract
    ; _≤ᵒ_ = _≤ᵒ_
    ; ≤ᵒ-id = ≤ᵒ-id
    ; ≤ᵒ-trans = ≤ᵒ-trans
    ; IsChild = iskid
    ; get-children = get-children
    ; get-parent = get-parent
    ; remObj = remObj
    ; rem-map = {! rem-map  !}
    ; addFS = addFS
    ; add-map = add-map
    }
```
 