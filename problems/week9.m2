if true or class see === Symbol then (
    see = method();
    see Ideal := I -> netList I_*
    );
mydenominator = method()
mygcd = method()
myfactors = method()

-- Find the denominator of the polynomial f
mydenominator RingElement := (f) -> (
    -- if f is a polynomial over a fraction field, gives the lcm of the denominators
    R := ring f;
    K := coefficientRing R;
    if instance(K, FractionField) then (
        denoms := (terms f)/leadCoefficient/denominator;
        lcm denoms
        )
    else 1_K
    )

-- Find the (monic) gcd of f and g.
mygcd(RingElement, RingElement) := (f,g) -> (
    if instance(coefficientRing ring f, FractionField) then (
        R := ring f;
        K := coefficientRing R;
        A := (coefficientRing K)[gens R, gens K];
        f1 := sub(f, A);
        g1 := sub(g, A);
        ans := sub(gcd(f1,g1), R);
        if leadCoefficient ans != 1 then (1/leadCoefficient ans) * ans else ans
    ) else gcd(f,g)
  )

-- Find the factors of f, in the form
-- {{p1, m1}, {p2, m2}, ..., {pr, mr}}
-- actually, a field element might be present too...
-- we should probably not consider that?
myfactors RingElement := (f) -> (
    -- TODO: need to restore lead coefficient too. (Maybe add in the denominator as an element of the field?)
    -- and make sure all factors are monic, even in the second case.
    if instance(coefficientRing ring f, FractionField) then (
        R := ring f;
        K := coefficientRing R;
        A := (coefficientRing K)[gens R, gens K];
        -- need to clear denominators of f first.
        d := mydenominator f;
        if d != 1 then f = d*f;
        f1 := sub(f, A);
        facs := factor f1;
        facs = facs//toList/toList;
        ans := for g in facs list (
            h := sub(g#0, R);
            h = if leadCoefficient h != 1 then (1/leadCoefficient h) * h else h;
            {h, g#1}
            )
    ) else (
        facs = factor f;
        facs = facs//toList/toList;
        facs
        )
    )

  univariate = method()

  -- if dim I == 0, v is a variable in the ring of I,
  -- compute the factors of a generator of I \cap k[v].
  -- ring of I should be k[x1, ..., xn], where k is
  -- a basic field or a fraction field.
  univariate(RingElement, Ideal) := (v, I) -> (
      elimvars := rsort toList (set (gens ring I) - set {v});
      J := eliminate(I, elimvars);
      if numgens J != 1 then error "my logic is wrong: J doesn't have one generator!";
      myfactors J_0
      )

  -- same as univariate, except it returns a list of v => list of factors,
  -- one for each variable v of the ring of I.
  univariates = method()
  univariates(Ideal) := (I) -> (
      for v in gens ring I list v => univariate(v, I)
      )
  
end--
restart
load "week9.m2"

----------------
-- Problem A ---
----------------
-- A zero dimensional ideal
-- Consider the following ideal, which arises from a Kuramoto
-- oscillator problem (I might describe this construction in class).
kk = QQ
 -- kk = ZZ/101 -- choose one of these two fields, and comment out the other one
R = kk[x_1..y_4];
gens R

I = ideal(-y_2-y_3-y_4,
  x_3*y_1+x_4*y_1-x_1*y_3-x_1*y_4,
  x_4*y_2-x_2*y_4+y_2,
  -x_3*y_1+x_1*y_3+x_4*y_3-x_3*y_4+y_3,
  -x_4*y_1-x_4*y_2-x_4*y_3+x_1*y_4+x_2*y_4+x_3*y_4+y_4,
  x_1^2+y_1^2-1,
  x_2^2+y_2^2-1,
  x_3^2+y_3^2-1,
  x_4^2+y_4^2-1)

(dim I, degree I)
-- Problem: compute a primary decomposition of I, using methods from class.
-- Here is Macaulay2's result:
minimalPrimes I
primaryDecomposition I
-- actually, we see lots of components from setting each x_i^2 = 1.
easy = ideal(x_1^2-1,
    x_2^2-1,
    x_3^2-1,
    x_4^2-1,
    y_1,y_2,y_3,y_4)
I1 = I : easy
I2 = I : I1
I == intersect(I1, I2)
(dim I1, degree I1)
(dim I2, degree I2) -- make sure you can do this one too!
-- remaining problem: use the methods in class to find
-- a primary decomposition of I1.
-- You may use the functions in this file!

-----------------
-- Exercise A1 --
-----------------
-- Try the functions univariate, univariates out to make sure you understand what they return
-- and what they do.  Use them on (perhaps) I1 or I.
netList univariates(I1)
-----------------
-- Exercise A2 --
-----------------
-- Find a primary decomposition, and the minimal primes, for I1 and I.
for fac in univariate(x_1, I1) list print fac
J1s = for fac in univariate(x_1, I1) list trim (I1 + ideal(fac_0))
intersect(J1s) == I1
J1s/degree
J1s_0

Rlex = newRing(R, MonomialOrder => Lex)
Ls = for J in J1s list sub(J, Rlex)
see ideal groebnerBasis Ls_0 -- is in normal position
see ideal groebnerBasis Ls_1 -- is prime
see ideal groebnerBasis Ls_2 -- 
univariate(y_4, Ls_1)
univariate(y_4, Ls_2)

-----------------
-- Problem A-1 --
-----------------
  R = QQ[a,b,c,d,e]
  I = ideal(
    a+b+c+d+e,
    d*e + c*d + b*c + a*e + a*b,
    c*d*e + b*c*d + a*d*e + a*b*e + a*b*c,
    b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d,
    a*b*c*d*e - 1)
  (dim I, degree I)
  minimalPrimes I
  dim I
  primaryDecomposition I
  I == radical I

  facs = univariate(a, I)
  netList facs
  L1 = for fac in facs list (
      trim ideal groebnerBasis (
        (I + ideal(fac#0))
        ))
  L1/dim
  L1/degree
  facs = univariate(b, L1_0)
  netList oo
  L2 = for fac in facs list (
      trim ideal groebnerBasis (
        (L1_0 + ideal(fac#0))
        ))

  splitRadical = method() 
  splitRadical(RingElement, Ideal) := List => (v, I) -> (
      facs := univariate(v, I);
      for fac in facs list 
      trim ideal groebnerBasis (
        (I + ideal(fac#0))
        )
      )
  splitRadical(RingElement, List) := List => (v, L) -> (
      flatten for I in L list splitRadical(v, I)
      )

  splitRadical(List, Ideal) := List => (varlist, I) -> (
      L := {I};
      for v in varlist do (
          L = splitRadical(v, L)
          );
      L
      )
///
L1 = splitRadical(a, I)
intersect L1 == I
netList L1
L2 = splitRadical(b, L1)
intersect L2 == I
#L2
L3 = splitRadical(c, L2)
#L3
netList L3
L4 = splitRadical(d, L3)
#L4
L5 = splitRadical(e, L4)

Rlex = newRing(R, MonomialOrder => Lex)
L5lex = for i in L5 list ideal groebnerBasis sub(i, Rlex)
L5/isPrime

use R
splitRadical({a,b,c,d,e}, I)
///
----------------
-- Problem B ---
----------------
-- A positive dimensional ideal

kk = ZZ/101
kk = QQ
R = kk[x_1..y_4]
I = ideal(
    -y_2-y_3-y_4,
    x_3*y_1+x_4*y_1-x_1*y_3-x_1*y_4,
    x_3*y_2+x_4*y_2-x_2*y_3-x_2*y_4+y_2,
    -x_3*y_1-x_3*y_2+x_1*y_3+x_2*y_3+x_4*y_3-x_3*y_4+y_3,
    -x_4*y_1-x_4*y_2-x_4*y_3+x_1*y_4+x_2*y_4+x_3*y_4+y_4,
    x_1^2+y_1^2-1,
    x_2^2+y_2^2-1,
    x_3^2+y_3^2-1,
    x_4^2+y_4^2-1)
elapsedTime minimalPrimes I -- very fast, over ZZ/101 or QQ
I == radical I -- not true!
elapsedTime compsI = primaryDecomposition I -- .7 sec over ZZ/101 or over QQ.

compsI/dim
compsI/degree
compsI/radical/degree
compsI_7

dim I -- not zero dimensional!
degree I

-----------------
-- Exercise B1 --
-----------------
-- Once you create a fraction field k(u)[x\u], 
-- try the functions mydenominator, mygcd, myfactors out to make sure you understand what they return
-- and what they do.


-----------------
-- Exercise B2 --
-----------------
-- Find a primary decomposition, and the minimal primes, for I.

-- to get started, use `independentSets`
-- WARNING: read the documentation for what they return.
indepsets = independentSets I -- very confusing output... Read the doc about it.
U = rsort support indepsets#0 -- take the support of the first of the 2 (max size) independent sets
Y = rsort toList(set gens R - set U)
gens R
A = kk[U]
B = frac A
C = A[Y, Join => false, MonomialOrder => Lex] -- the Join is here to not make this ring doubly graded.
D = B (monoid C)
ID = sub(I, D)
see ideal gens gb ID
netList univariates ID

IC = sub(I, C)
LTI = flatten entries leadTerm(1, IC)
netList LTI
LTC = LTI/leadCoefficient
h = lcm oo
factor h
myfactors h
h = sub(y_1 * (16*y_1^2 + 9), R)
I1 = saturate(I, h)
-- what should h be replaced by so that
use R
I1 == saturate(I, y_1) -- true!!  Don't need the more complicated h...
I1 == I : y_1^2
I1 == I : y_1^3 -- true!
I2 = I + ideal(y_1^3)
dim I1
dim I2
I == intersect(I1, I2)
isPrime I1
isPrime I2

ID = sub(I, D)
see ideal groebnerBasis ID
