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
    if not all(indep, v -> ring v === R and index v =!= null)
    then error "expected a list of variables in the given ring";
    fibervars := rsort toList((set gens R) - set indep);
    (coefficientRing R)[indep][fibervars, Join => false, MonomialOrder => Lex]
    )
  
end--
restart
load "week11.m2"
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
    saturate(J, denoms)
    )

-- let's write an extension-contraction algorithm
-- let's find the integer m s.t. I = sat(I) + (I + h^m)
 
