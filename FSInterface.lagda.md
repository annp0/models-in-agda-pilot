```agda
module FSInterface where

open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open Eq.≡-Reasoning -- everything
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (¬?; _×-dec_)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)
open import Tree using (Tree; TreeList; []; _∷_; TreeShape;
    V; L′; _⇒_; get; V-∀; N; node; _∈_; here; there; status;
    get-list; self; tran; child; _+ᵖ_; get-+ᵖ; get-status;
    _∈ᶜ_; ≤ˢ-max-eq; ≡-≤ˢ; erase; erase-V; add-shape; add-V; add;
    add-≡; live; erased; Status; _≰ᵖ_; erase-other; as-↑;
    add-other; add-shape-N; _≤ᵖ_; ≤ᵖ-id; ≤ᵖ-trans; _≡ᵐ_; _≡ᵐ?_; 
    refl; _≡?_; N?; ≤ᵖ-+ᵖ; ≤ᵖ-≡)
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
        -- what is the root?
        -- this also implicitly states that the root is unique
        root : ∀ {a} → FSObj a
        -- what is the information that an object could contain?
        Info : Set

        -- Functions & properties related to objects
        -- equality between objects
        _≡ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set 
        -- this relation should be an equivalence relation
        ≡ᵒ-prop : ∀ {a} → IsEquivalence (_≡ᵒ_ {a})
        -- this should be decidable
        _≡ᵒ?_ : ∀ {a} (obj₁ obj₂ : FSObj a) → Dec (obj₁ ≡ᵒ obj₂) 
    
    -- and now IsNotRoot is decidable (as it should be)
    -- this also implies that an obj is either the root or not the root, no middle ground
    IsNotRoot : ∀ {a} → FSObj a → Set
    IsNotRoot obj = ¬ (obj ≡ᵒ root)
    IsNotRoot? : ∀ {a} (obj : FSObj a) → Dec (IsNotRoot obj)
    IsNotRoot? obj = ¬? (obj ≡ᵒ? root)

    field
        -- what is a directory? (should be decidable)
        IsDir : ∀ {a} → FSObj a → Set 
        IsDir? : ∀ {a} → (obj : FSObj a) → Dec (IsDir obj)
        -- also, root should be a dir
        RootIsDir : ∀ (a : A) → IsDir (root {a})
        -- extracting the information that an object processes
        extract : ∀ {a} → FSObj a → Info

        -- `contained` relation (should be a pre order)
        _≤ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
        -- properties that a pre order should satisfy
        ≤ᵒ-prop : ∀ {a} → IsPreorder (_≡ᵒ_ {a}) (_≤ᵒ_ {a}) 
    
    -- Previous IsNotContained
    _≰ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
    _≰ᵒ_ obj₁ obj₂ = ¬ (obj₁ ≤ᵒ obj₂)

    field
        -- when do we say an object is a child of another object?
        IsChild : ∀ {a} → FSObj a → FSObj a → Set
        -- how does IsChild interact with the rest of the interface?
        IsChild-≤ᵒ : ∀ {a} {par kid : FSObj a} → IsChild par kid → par ≤ᵒ kid
        IsChild-IsDir : ∀ {a} {par kid : FSObj a} → IsChild par kid → IsDir par

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
        add-map : ∀ {a} → (objm : FSObj a) → (idom : IsDir objm) 
            → (objo : FSObj a) → objo ≰ᵒ objm → (b : A)
            → Σ[ objn ∈ FSObj (addFS objm idom b) ] extract objo ≡ extract objn
```   

Now we have an interface, it is time to implement this interface based on
the tree model we already have.

```agda
-- A file system is a tree that's (1) valid (2) with live root (3) root is a node
record FS : Set where
    constructor fs
    field
        -- TreeShape of the fs
        shape : TreeShape
        -- The root tree of the fs (f-root)
        froot : Tree shape 
        -- The tree is valid
        valid : V froot
        -- The tree has live root
        isliv : L′ froot
        -- The tree's root is a directory (node)
        isdir : N shape
open FS

-- An Object is a live object of the tree
-- using datatypes could block eta-equality help unification
-- so we may use implicits freely 
data FSObj (fx : FS) : Set where
    fsobj : (y : TreeShape) → (x⇒y : (shape fx) ⇒ y) → L′ (get x⇒y (froot fx)) → FSObj fx

-- The root is just the root object of the tree
root : ∀ {fx} → FSObj fx
root {fx} = fsobj (shape fx) self (isliv fx)

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

-- obvious but helpful
p-contra : ∀ {x y z a b} → tran {y} {x} {z} a b ≡ᵖ self → ⊥
p-contra ()

-- decidable algorithm
_≡ᵖ?_ : ∀ {x y z} → (x⇒y : x ⇒ y) → (x⇒z : x ⇒ z) → Dec (x⇒y ≡ᵖ x⇒z) 
self ≡ᵖ? self = yes refl
self ≡ᵖ? tran _ _ = no λ eq → p-contra (≡ᵖ-sym eq)
tran _ _ ≡ᵖ? self = no λ eq → p-contra eq
-- ≡ᵐ comes in handy
tran (child b∈xs) b⇒y ≡ᵖ? tran (child c∈xs) c⇒z with b∈xs ≡ᵐ? c∈xs 
... | yes refl = help
    where
        help : Dec (tran (child b∈xs) b⇒y ≡ᵖ tran (child c∈xs) c⇒z)
        help with b⇒y ≡ᵖ? c⇒z 
        ... | yes refl = yes refl
        ... | no neq = no λ {refl → neq refl}
... | no neq = no λ {refl → neq refl}

-- equality for objects, 
-- since our fs objects contain proofs now, we need an equality
-- with proof irrelavance (i.e. simply just don't care about it)
_≡ᵒ_ : ∀ {fx : FS} → FSObj fx → FSObj fx → Set
(fsobj y x⇒y pf) ≡ᵒ (fsobj z x⇒z pf′) = y ≡ z × (x⇒y ≡ᵖ x⇒z)

≡ᵒ-id : ∀ {fx} {obj : FSObj fx} → obj ≡ᵒ obj
≡ᵒ-id {_} {fsobj _ _ _} = refl , refl

≡ᵒ-trans : ∀ {fx} {obj₁ obj₂ obj₃ : FSObj fx} → obj₁ ≡ᵒ obj₂ → obj₂ ≡ᵒ obj₃ → obj₁ ≡ᵒ obj₃
≡ᵒ-trans {_} {fsobj _ _ _} {fsobj _ _ _} {fsobj _ _ _}
    (a=b , pa=b) (b=c , pb=c) = trans a=b b=c , ≡ᵖ-trans pa=b pb=c

≡ᵒ-sym : ∀ {fx : FS} {obj₁} {obj₂ : FSObj fx} → obj₁ ≡ᵒ obj₂ → obj₂ ≡ᵒ obj₁
≡ᵒ-sym {_} {fsobj _ _ _} {fsobj _ _ _} (refl , refl) = refl , refl

-- derived decidable
_≡ᵒ?_ : ∀ {fx : FS} (ox oy : FSObj fx) → Dec (ox ≡ᵒ oy)
fx@(fsobj y x⇒y _) ≡ᵒ? fy@(fsobj z x⇒z _) = (y ≡? z) ×-dec (x⇒y ≡ᵖ? x⇒z)

IsDir : ∀ {fx} → FSObj fx → Set
IsDir (fsobj y _ _) = N y

IsDir? : ∀ {fx} → (obj : FSObj fx) → Dec (IsDir obj)
IsDir? (fsobj y _ _) = N? y

rootisdir : ∀ {fx} → IsDir (root {fx})
rootisdir {fx} = isdir fx

extract : ∀ {fx} → FSObj fx → Status
extract {fx} (fsobj _ x⇒y _) = get-status x⇒y (froot fx)

_≤ᵒ_ : ∀ {fx} → FSObj fx → FSObj fx → Set
(fsobj _ x⇒y _) ≤ᵒ (fsobj _ x⇒z _) = x⇒y ≤ᵖ x⇒z

≤ᵒ-id : ∀ {fx} {obj₁ obj₂ : FSObj fx} → obj₁ ≡ᵒ obj₂ → obj₁ ≤ᵒ obj₂
≤ᵒ-id {_} {fsobj _ _ _} {fsobj _ _ _} (refl , refl) = ≤ᵖ-id

≤ᵒ-trans : ∀ {fx} {obj₁ : FSObj fx} {obj₂ obj₃} →
    obj₁ ≤ᵒ obj₂ → obj₂ ≤ᵒ obj₃ → obj₁ ≤ᵒ obj₃ 
≤ᵒ-trans {_} {fsobj _ _ _} {fsobj _ _ _} {fsobj _ _ _}
    a b = ≤ᵖ-trans a b

-- better definition for ischild
ischild : ∀ {fx} → FSObj fx → FSObj fx → Set
ischild (fsobj y x⇒y _) (fsobj z x⇒z _) = 
    Σ[ z∈y ∈ z ∈ᶜ y ] x⇒z ≡ x⇒y +ᵖ tran z∈y self

ischild-≤ᵒ : ∀ {fx} {a b : FSObj fx} → ischild a b → a ≤ᵒ b
ischild-≤ᵒ {_} {fsobj _ x⇒y _} {fsobj _ x⇒z _} (z∈y , pf) = ≤ᵖ-≡ ≤ᵖ-+ᵖ (sym pf)

ischild-dir : ∀ {fx} {a b : FSObj fx} → ischild a b → IsDir a
ischild-dir {_} {fsobj _ _ _} {fsobj _ _ _} (child _ , _ ) = node

get-children : ∀ {fx} → (obj : FSObj fx) → IsDir obj 
    → List (Σ[ kid ∈ (FSObj fx) ] ischild obj kid)
get-children {fx} obj@(fsobj (node ys) x⇒y pv) node = map-∈ gen-∈
    where
        x = shape fx
        tx = froot fx
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
            → List (Σ[ kid ∈ (FSObj fx) ] ischild obj kid)
        map-∈ [] = []
        map-∈ ((z , z∈ys) ∷ rest) with status (get-list z∈ys (get-tl ty)) in eq
        ... | live = ((fsobj z (x⇒y +ᵖ tran (child z∈ys) self)
            (begin get-status (x⇒y +ᵖ tran (child z∈ys) self) tx 
            ≡⟨ cong status (get-+ᵖ x⇒y (tran (child z∈ys) self) tx) ⟩ 
            get-status (tran (child z∈ys) self) ty 
            ≡⟨ cong status (cong (get (tran (child z∈ys) self)) (guide ty)) ⟩
            eq)) , child z∈ys , refl) ∷ map-∈ rest
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
                p-contra (≡ᵖ-trans (≡ᵖ-sym (≡-≡ᵖ eq refl)) eqp)
        in ts , tran z∈ᶜx path , kid , 
            cong (tran z∈ᶜx) (trans (sym eq) pf)

-- get parent
get-parent : ∀ {fx} → (obj : FSObj fx) → ¬ (obj ≡ᵒ (root {fx})) 
    → Σ[ par ∈ FSObj fx ] ischild par obj
get-parent (fsobj x self eq) neq = ⊥-elim (neq (refl , refl))
get-parent {fx} (fsobj _ x⇒z@(tran _ _) lz) neq = let
        y , x⇒y , z∈y , pf = gp-help x⇒z λ ()
        tx = froot fx
        vx = valid fx
    in
        fsobj y x⇒y 
        (≤ˢ-max-eq (≡-≤ˢ (sym lz) 
        (≡-≤ˢ (cong (λ x → get-status x tx) pf)
        (vx x⇒y (tran z∈y self))))) , 
        (z∈y , pf)

remObj : ∀ {fx} → (obj : FSObj fx) → ¬ (obj ≡ᵒ root) → FS
remObj (fsobj x self eq) neq = ⊥-elim (neq (refl , refl))
remObj {fs x tx@(node _ _) vx lx dx} (fsobj y x⇒y@(tran (child _) _) eq) neq = record { 
        shape = x 
    ;   froot = erase x⇒y tx 
    ;   valid = erase-V x⇒y tx vx 
    ;   isliv = lx 
    ;   isdir = dx }

rem-map : ∀ {fx} → (objr : FSObj fx) → (nr : ¬ (objr ≡ᵒ root ))
    → (objo : FSObj fx) → ¬ (objr ≤ᵒ objo)
    → Σ[ objn ∈ FSObj (remObj objr nr) ] extract objo ≡ extract objn
rem-map {fs x tx vx _ _} (fsobj x self eq) neq _ _ = ⊥-elim (neq (refl , refl))
rem-map {fs x tx@(node _ _) _ _ _} (fsobj y x⇒y@(tran (child _) _) _) nr (fsobj a x⇒a la) nc 
    = (fsobj a x⇒a (trans (sym eq) la)) , eq
    where
        eq = erase-other x⇒y x⇒a nc tx

addFS : ∀ {fx} → (obj : FSObj fx) → IsDir obj → FS → FS
addFS {fs x tx vx lx nx} (fsobj y x⇒y ly) node (fs a fa va la _) 
    = fs (add-shape nx node x⇒y a) (add x⇒y tx fa) (add-V x⇒y vx va ly) 
    (trans (add-≡ nx node tx fa x⇒y) lx) (add-shape-N nx node x⇒y) 

add-map : ∀ {fx} → (objm : FSObj fx) → (idom : IsDir objm)
    → (objo : FSObj fx) → ¬ (objo ≤ᵒ objm) → (fa : FS)
    → Σ[ objn ∈ FSObj (addFS objm idom fa) ] extract objo ≡ extract objn
add-map {fs x tx vx _ nx} (fsobj y x⇒y ly) node (fsobj b x⇒b lb) nc (fs a fa va _ _) = 
    fsobj b (as-↑ x⇒y x⇒b nc a) (trans (sym eq) lb) , eq
    where
        eq = add-other {_} {_} {nx} {node} x⇒y x⇒b nc tx fa ly

isequi : ∀ {fx : FS} → IsEquivalence (_≡ᵒ_ {fx})
isequi = record { refl = ≡ᵒ-id ; sym = ≡ᵒ-sym ; trans = ≡ᵒ-trans }

_ : IsFS FS
_ = record { FSObj = FSObj
    ; root = root
    ; Info = Info
    ; _≡ᵒ_ = _≡ᵒ_
    ; IsDir = IsDir
    ; RootIsDir = λ fx → rootisdir {fx} 
    ; extract = extract
    ; _≤ᵒ_ = _≤ᵒ_
    ; IsChild = ischild
    ; get-children = get-children
    ; get-parent = get-parent
    ; remObj = remObj
    ; rem-map = rem-map
    ; addFS = addFS
    ; add-map = add-map
    ; ≡ᵒ-prop = record { refl = ≡ᵒ-id ; sym = ≡ᵒ-sym ; trans = ≡ᵒ-trans }
    ; ≤ᵒ-prop = record { isEquivalence = isequi ; reflexive = ≤ᵒ-id ; trans = ≤ᵒ-trans }
    ; IsChild-≤ᵒ = ischild-≤ᵒ
    ; IsChild-IsDir = ischild-dir
    ; _≡ᵒ?_ = _≡ᵒ?_
    ; IsDir? = IsDir?
    }
```
 
