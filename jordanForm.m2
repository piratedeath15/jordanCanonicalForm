-- jordanForm.m2
-- Colin E. Martin
-- 11/27/18
exactEigenvalues = method()
exactEigenvalues Matrix := M -> (
    
   kk := M.ring;
   R := kk[x];
   N := sub(M,R);
   factorList := toList factor det(Mminus(N,x));
   if any(factorList, f -> (degree f#0)#0 > 1) then error "Eigenvalues outside of field.";
   eigenList := unique apply(factorList, f -> -1*((f#0)-x));
   proj = map(kk,R,gens kk);
   eigenList/proj
)


Mminus = method()
Mminus (Matrix,ZZ) :=
Mminus (Matrix,QQ) :=
Mminus (Matrix,RingElement) := (M,lambda) -> (    
   --if not liftable(lambda,M.ring) then error("Scalar not liftable to matrix ring.");
   M -(lambda*id_(M.source))
)

basisEigenspace = method()
basisEigenspace (Matrix, ZZ) :=
basisEigenspace (Matrix, QQ) :=
basisEigenspace (Matrix, RingElement)  := (M,lambda) -> (
   --if lambda.ring  =!= M.ring then error "Expected matrix over field of eigenvalue"; 
   Ker := ker Mminus(M,lambda);
   basisList := apply(numgens Ker, i -> (mingens  Ker)_{i}); -- is there an easier way to get a list of column vectors?
   basisList
)

basisGeneralEigenspace = method()
basisGeneralEigenspace (Matrix,ZZ) :=
basisGeneralEigenspace (Matrix,QQ) :=
basisGeneralEigenspace (Matrix,RingElement) := (M,lambda) -> (
   --Mminus := M-(lambda*id_(M.source));
   n := numgens source M;
   Ker := ker (Mminus(M,lambda))^n;
   basisList := apply(numgens Ker, i -> (mingens Ker)_{i});
   basisList
   )

span = method()
span List := matList -> (
    
   mat :=  matrix {matList};
   image mat
   )

extendBasis = method(Options => {Inc => false})
extendBasis (Module,List) := opts -> (V, initBasis) -> (
    
   --if any(initBasis, v -> (module vector v) != V) then error "Basis not contained by vector space.";
   if initBasis === {} then return apply(rank V, i -> (mingens V)_{i});
   subV := span initBasis;
   quotV := V/subV;
   if quotV == 0 and opts#Inc then return initBasis else if quotV == 0 then return {};
   basisQuotV := apply(rank quotV, i ->(mingens quotV)_{i});
   if opts#Inc === true then return initBasis|basisQuotV;
   basisQuotV
   )

pCalculator = method() -- Could I have just read off the number of times lambda shows up in the command eigenvalues M?
pCalculator (Matrix,ZZ) :=
pCalculator (Matrix,QQ) :=
pCalculator (Matrix,RingElement) := (M,lambda) -> (
   
   E := span basisEigenspace(M,lambda);
   Mmin := Mminus(M,lambda);
   p:= 1;
   range := image Mmin;
   while intersect{E, range} != 0 do (

       p = p+1;
       range = image (Mmin^p);
       
       
       );
   p
)




buildTheChain = method()
buildTheChain (Matrix, Matrix, ZZ) := (v,T,p) -> (
    
   w := v // T^p;
   apply(p+1, i -> (T^i)*w)
)   

computeJordanSubBasis = method()
computeJordanSubBasis (Matrix,ZZ) :=
computeJordanSubBasis (Matrix,QQ) :=
computeJordanSubBasis (Matrix,RingElement) := (M,lambda) -> (
   Mmin := Mminus(M,lambda);
   p := pCalculator(M,lambda) -1;
   E := span basisEigenspace(M,lambda);
   S := {}; --mingens intersect{E, image(Mmin^p)};
   workingBasis := {};
   newS := {};
   --eigenIntersect := source Mmin;
   while p >= 0 do (
       eigenIntersect := intersect{(image (Mmin^p)),E};
       newS = extendBasis(eigenIntersect, workingBasis);
       workingBasis = extendBasis(eigenIntersect, workingBasis, Inc => true);
       --error "err";
       S = S | (reverse flatten( apply(newS, v -> buildTheChain(v,Mmin,p))));
       p = p-1;
       );  
S   
)

jordanBasis = method()
jordanBasis Matrix := M -> (
   
   --- eigenList := apply(toList eigenvalues M, c -> lift(c,M.ring));
   eigenList := exactEigenvalues M;
   distinctEigenList := reverse sort eigenList;
   matrix{flatten apply(distinctEigenList, e -> computeJordanSubBasis(M,e))}
)

jordanForm = method()
jordanForm Matrix := M -> (
    
    P := jordanBasis M;
    P^(-1)*M*P
)

end

---9a
restart
load "jordanForm.m2"
M = matrix{{3/1,2,1,2},{0,2,3,2},{0,0,3,4},{0,0,0,2}}
v = (basisEigenspace(M,2))_0
buildTheChain(v,Mminus(M,2),1)
    
    
exactEigenvalues M
basisEigenspace (M,3)
R = QQ[x]
M = sub(M,R)
f = factor det(M - x*id_(R^4))
solve(f,0)
basisEigenspace (M,2/1)
G3 = basisGeneralEigenspace(M,3)
G2 = basisGeneralEigenspace(M,2)
pCalculator(M,3)
pCalculator(M,2)
extendBasis(QQ^4,G3, Inc => true)

computeJordanSubBasis(M,2)
computeJordanSubBasis(M,3)
P = jordanBasis(M)
P^(-1)*M*P
---9b
restart
load "jordanForm.m2"
M = matrix{{9/1,0,0,1},{-1,8,0,-1},{0,1,7,0},{0,1,-1,8}}
P = jordanBasis(M)
computeJordanSubBasis(M,8)
P^(-1)*M*P
jordanForm(M)
R = QQ[x]
M = sub(M,R)
factor det(M - x*id_(R^4))


---FrankCode
restart
load "jordanForm.m2"
M = matrix {{25, 1, 1, 3, -3, -3, -3, -1, -1, -1, -1, -3, 1, 1, 1, 3},
     {-3, 17, 1, -9, 1, -3, -3, 3, 3, -1, -1, 1, -3, 1, 1, -1},
     {-1, 3, 7, 1, 3, -1, 3, -3, 1, -3, 1, -1, -1, 3, -1, 1},
     {1, 9, -3, 15, -3, -3, 1, 3, -1, -1, 3, 1, 1, 1, -3, -1},
     {-3, -3, -3, -1, 25, 1, 1, 3, -1, -1, -1, -3, 1, 1, 1, 3}, 
     {1, -3, -3, 3, -3, 17, 1, -9, 3, -1, -1, 1, -3, 1, 1, -1}, 
     {3, -1, 3, -3, -1, 3, 7, 1, 1, -3, 1, -1, -1, 3, -1, 1},
     {-3, -3, 1, 3, 1, 9, -3, 15, -1, -1, 3, 1, 1, 1, -3, -1},
     {-3, 1, 1, -1, -3, 1, 1, -1, 23, 3, 3, 5, 5, 1, 1, -1},
     {1, 1, 1, 3, 1, 1, 1, 3, -5, 19, 3, -7, 1, 1, 1, -5},
     {-1, -1, 3, 1, -1, -1, 3, 1, -3, 5, 9, 3, -1, -1, -5, 1},
     {1, -3, 1, -1, 1, -3, 1, -1, 3, 7, -5, 13, 1, 5, 1, -1},
     {3, -1, -1, 1, 3, -1, -1, 1, 5, 1, 1, -1, 23, 3, 3, 5},
     {-1, -1, -1, -3, -1, -1, -1, -3, 1, 1, 1, -5, -5, 19, 3, -7},
     {1/1, 1, -3, -1, 1, 1, -3, -1, -1, -1, -5, 1, -3, 5, 9, 3},
     {-1, 3, -1, 1, -1, 3, -1, 1, 1, 5, 1, -1, 3, 7, -5, 13}}
P = jordanBasis(M)
P^(-1)*M*P
R = QQ[x]
M = sub(M,R)
factor det(Mminus(M,x))

