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

  -- For a dimension zero ideal, here is how we can break it down   
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

  splitRadical(Ideal) := List => (I) -> (
      L := {I};
      for v in gens ring I do (
          L = splitRadical(v, L)
          );
      L
      )

findMaxIndepSet = method()
findMaxIndepSet Ideal := List => I -> (
    support first independentSets(I, Limit => 1)
    )

extensionRing = method()
extensionRing(Ring, List) := (R, indep) -> (
    if not all(indep, v -> ring v === R and index v =!= null)
    then error "expected a list of variables in the given ring";
    fibervars := rsort toList((set gens R) - set indep);
    K := frac((coefficientRing R)[indep]);
    K[fibervars, MonomialOrder => Lex] -- maybe another order would be better?
    )

productOrderRing = method()
productOrderRing(Ring, List) := (R, indep) -> (
    if not all(indep, v -> ring v === R and index v =!= null) then (
        error "expected a list of variables in the given ring";
        );
    fibervars := rsort toList((set gens R) - set indep);
    (coefficientRing R)[indep][fibervars, Join => false, MonomialOrder => Lex]
    )

findFlattener = method()
findFlattener Ideal := (I) -> (
    -- assumed: I is in a product ring.
    -- find the squarefree part of the LCM of the lead coeffs
    G := flatten entries groebnerBasis I;
    h := lcm for g in G list leadCoefficient g;
    facs := factor h;
    facs = facs//toList/toList;
    for x in facs list if # support x#0 == 0 then continue else x#0
)

handleSplit = (I) -> (
    R := ring I;
    indep := findMaxIndepSet I;
    Rprod := productOrderRing(R, indep);
    Ip := sub(I, Rprod);
    hs := findFlattener Ip;
    hs = apply(hs, h -> sub(h, R));
    Rfrac := extensionRing(R, indep);
    Ifrac := sub(I, Rfrac);
    (ideal groebnerBasis Ifrac, hs)
)

contractToPolynomialRing = method()
contractToPolynomialRing(Ideal, Ring) := Ideal => (I, R) -> (
    -- I is an ideal in k(u)[x\u], 0-dimensional?
    -- R is k[x]
    -- returns then ideal I \cap R
    gbI := ideal groebnerBasis I; -- reduced GB of I.
    denoms := gbI_*/mydenominator;
    denom := lcm denoms; -- this has an awful integeer part over QQ...
    denom = sub(denom, R);
    J := ideal for f in gbI_* list sub((mydenominator f) * f, R);
    saturate(J, denom)
    )

end--
restart
load "week12.m2"

---------------
-- Example 0 --
-- independent sets
---------------
R = ZZ/32003[a..d]
I = monomialCurveIdeal(R, {1,2,3})
I = ideal(I_0, I_1)
leadTerm I
independentSets I
radical ideal leadTerm I
minimalPrimes oo

-- Use {a,d}
use R
Rfrac = extensionRing(R, {a,d})
Ie = sub(I, Rfrac)
Ge = ideal groebnerBasis Ie
see Ge
Ie0 = sub(ideal(Ge_0, d * Ge_1), R)
use R
saturate(Ie0, d)
I1 = contractToPolynomialRing(Ie, R)
I2 = trim(I + ideal(d))
primaryDecomposition I2
I == intersect(I1, ideal(c,d), ideal(b, d, c^2))
I == intersect(I1, ideal(c,d))
isSubset(I1, ideal(b, d, c^2))


-- Use {a,b}
use R
Rfrac = extensionRing(R, {a,b})
Ie = sub(I, Rfrac)
Ge = ideal groebnerBasis Ie
see Ge
Ie0 = sub(ideal(Ge_0 * a^2, b * Ge_1), R)
use R
saturate(Ie0, b*a) == I
L = splitRadical Ge
I1 = sub(L_0, R)
use ring Ie
use coefficientRing oo
J = sub(ideal(a^2*(L_1_0), a*(L_1_1)), R)
use R
I2 = saturate(J, a)
I == intersect(I1, I2)
ideal groebnerBasis L_1

---------------
-- Example 1 --
---------------
R = ZZ/32003[a..d]
I = ideal(a*c^2-b^2*d,b^3-a^2*c)

---------------
-- Example 2 --
---------------
R = ZZ/32003[b,s,t,u,v,w,x,y,z]
I = ideal(
    s*u-b*v,
    t*v-s*w,
    v*x-u*y,
    w*y-v*z)

---------------
-- Example 3 --
---------------
-- positive dimensional from oscillators
-- not radical either...
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

----------------
-- Example 4 ---
----------------
-- zero dimensional
restart
needs "./week11.m2"
  R = QQ[a,b,c,d,e]
  I = ideal(
    a+b+c+d+e,
    d*e + c*d + b*c + a*e + a*b,
    c*d*e + b*c*d + a*d*e + a*b*e + a*b*c,
    b*c*d*e + a*c*d*e + a*b*d*e + a*b*c*e + a*b*c*d,
    a*b*c*d*e - 1)

---------------
-- Example ----
-- 2x2 permanents of a 3x3 generic matrix
-- this one has several cautionary tales...
---------------
R = ZZ/32003[b,s,t,u,v,w,x,y,z]
I = ideal(
    b*v+s*u,
    b*w+t*u,
    s*w+t*v,
    b*y+s*x,
    b*z+t*x,
    s*z+t*y,
    u*y+v*x,
    u*z+w*x,
    v*z+w*y)
primaryDecomposition I
findMaxIndepSet I
use R
Rprod = productOrderRing(R, {b, s, t})
gbI = ideal groebnerBasis sub(I, Rprod)
gbI_*/leadCoefficient//lcm
use R
RK = extensionRing(R, {b,s,t})
sub(gbI, RK)
ideal for a in oo_* list 1/(leadCoefficient a) * a
see oo
use R
saturate(I, b*s*t)
saturate(I, b*s*t) == I : (b*s*t)
see ideal groebnerBasis sub(I, RK)
use R
I1 = saturate(I, b*s*t)
I2 = I + ideal(b*s*t)
I == intersect(I1, I2)
primaryDecomposition I2

findMaxIndepSet I2
use R
Rprod = productOrderRing(R, {b, s, v})
gbI2 = ideal groebnerBasis sub(I2, Rprod)
gbI2_*/leadCoefficient//lcm
use R
saturate(I2, b*s*v) == I2 : (b*s*v)
primaryDecomposition(I2 + ideal(b*s*v))
-- oh no, extra primary components!
-- maybe try to find the radical first...


------------------------------
-- Extra ---------------------
------------------------------

-- let's write an contraction algorithm
-- this is only a start, needs to be checked!


-- let's write an extension-contraction algorithm
-- let's find the integer m s.t. I = sat(I) + (I + h^m)
 
-- Let's write the following function:
-- input: ideal I
-- output: split off an indep set, write I as intersection of the components of the indep set, and one other.

-- steps for minimal primes
--  1. choose an indep set
--  2. create the product ring Rprod
--  3. compute a GB in this ring, use that to determine h s.t. I^{ec} = saturate(I, h) = I : h^\ell.
--  4. compute I^e
--    4a. compute its radical
--    4b. split into primes
--    4c. for each of these, J, find its contraction J^c.
--    this gives us I^{ec}.
--  5. Induct by considering (I, h), whose dimension has dropped by 1.

R = ZZ/32003[b,s,t,u,v,w,x,y,z]
I = ideal(
    s*u-b*v,
    t*v-s*w,
    v*x-u*y,
    w*y-v*z)

-- do a couple by hand...
indep = findMaxIndepSet I -- {b, t, u, w, x, z}
Rprod = productOrderRing(R, indep)
describe Rprod
Ip = sub(I, Rprod)
hs = findFlattener Ip
groebnerBasis Ip
hs = hs/(h -> sub(h, R))
I1 = I : product hs
use R
I : ((w*x-u*z)*(w*x-u*z)) == I1
I2 = I + ideal((w*x-u*z)*(w*x-u*z))
I == intersect(I1, I2) -- true

indep = findMaxIndepSet I2
Rprod = productOrderRing(R, indep)
describe Rprod
I2p = sub(I2, Rprod)
hs = findFlattener I2p
groebnerBasis I2p
hs = hs/(h -> sub(h, R))
H = product hs
I21 = I2 : H
I22 = I2 + ideal H
I2 == intersect(I21, I22) -- true
I == intersect(I1, I21, I22)

indep = findMaxIndepSet I22
Rprod = productOrderRing(R, indep)
describe Rprod
I22p = sub(I22, Rprod)
hs = findFlattener I22p
groebnerBasis I22p
hs = hs/(h -> sub(h, R))
H = product hs
I221 = saturate(I22, H)
I222 = I22 + ideal H
I22 == intersect(I221, I222) -- true
I == intersect(I1, I21, I221, I222)

dim I222

indep = findMaxIndepSet I222
Rprod = productOrderRing(R, indep)
describe Rprod
I222p = sub(I222, Rprod)
hs = findFlattener I222p
groebnerBasis I222p
hs = hs/(h -> sub(h, R))
H = product hs
I2221 = saturate(I222, H)
I2221 == I222 : H
I2221 == I222 : H^2
I2222 = I222 + ideal H^2
I222 == intersect(I2221, I2222) -- true
I == intersect(I1, I21, I221, I2221, I2222)

isSubset(intersect(I1, I21, I221, I2221), I2222)
I2222
dim oo


(Ie, H) = handleSplit I
contractToPolynomialRing(Ie, R)
J1 = contractToPolynomialRing(Ie, R)
J1 == I : product H
K1 = I + ideal product H
I == intersect(J1, K1)

-- split K1
(Ke, H) = handleSplit K1
J2 = contractToPolynomialRing(Ke, R)
J2 == K1 : product H
K2 = K1 + ideal product H
I == intersect(J1, J2, K2)

-- split K2
(Ke, H) = handleSplit K2
J3 = contractToPolynomialRing(Ke, R)
J3 == K2 : product H
K3 = K2 + ideal product H
I == intersect(J1, J2, J3, K3) 

-- split K3
(Ke, H) = handleSplit K3
J4 = contractToPolynomialRing(Ke, R)
J4 == K3 : product H
K4 = K3 + ideal product H
I == intersect(J1, J2, J3, J4, K4)
J1, J2, J3, J4

-- split K4
(Ke, H) = handleSplit K4
J5 = contractToPolynomialRing(Ke, R)
J5 == K4 : (product H)^2
K5 = K4 + ideal (product H)^2
I == intersect(J1, J2, J3, J4, J5, K5) 
J1, J2, J3, J4, J5
K5

-- split K5
(Ke, H) = handleSplit K5
J6 = contractToPolynomialRing(Ke, R)
J6 == K5 : (product H)
K6 = K5 + ideal (product H)
I == intersect(J1, J2, J3, J4, J5, J6, K6) 
J1, J2, J3, J4, J5, J6

-- split K6
(Ke, H) = handleSplit K6
J7 = contractToPolynomialRing(Ke, R)
J7 == K6 : (product H)^2
K7 = K6 + ideal (product H)^2
I == intersect(J1, J2, J5, K7) 

-- split K7
(Ke, H) = handleSplit K7
J8 = contractToPolynomialRing(Ke, R)
J8 == K7 : (product H)^2
K8 = K7 + ideal (product H)^2
I == intersect(J1, J2, J5, K8) -- J8 not needed
dim K8 == 5

-- split K8
(Ke, H) = handleSplit K8
J9 = contractToPolynomialRing(Ke, R)
J9 == K8 : (product H)^3
K9 = K8 + ideal (product H)^3
I == intersect(J1, J2, J5, K9) 
dim K9 == 5

-- split K9
(Ke, H) = handleSplit K9
J10 = contractToPolynomialRing(Ke, R)
J10 == K9 : (product H)^5
K10 = K9 + ideal (product H)^5
I == intersect(J1, J2, J5, K10)
dim K10 == 5

(Ke, H) = handleSplit K10
J11 = contractToPolynomialRing(Ke, R)
J11 == K10 : (product H)
K11 = K10 + ideal (product H)
I == intersect(J1, J2, J5, K11)
dim K11 == 5

(Ke, H) = handleSplit K11
J12 = contractToPolynomialRing(Ke, R)
J12 == K11 : (product H)^3
K12 = K11 + ideal (product H)^3
I == intersect(J1, J2, J5,  K12)
dim K12 == 4


