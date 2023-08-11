-- Computing unit groups of plane hyperelliptic curves over F_2

------------------------------
-- Helper functions
------------------------------

displayMessage := (fn, m) -> if debugLevel > 0 then printerr(fn | ": " | m)

updateStatus := m -> << "\r" << m << flush

deg = method()
deg RingElement := ZZ => f -> if f == 0 then -infinity else sum degree f
deg ZZ := ZZ => n -> 0

allPolys = method() -- returns all monic univariate polynomials of a given degree with 0/1 coefficients
allPolys (ZZ, PolynomialRing) := List => memoize((d, R) -> (
	if d < 0 then {0_R}
	else if d == 0 then {1_R}
	else flatten apply(allPolys(d-1, R), f -> {R_0*f, R_0*f + 1})
))

coprimePolys = method() -- returns all monic polynomials of degree d coprime to F
coprimePolys (ZZ, RingElement) := List => (d, F) -> (
	R := ring F;
	irreducibles := (toList factor F)/toList/first;
	allPolys(d, R) - set flatten apply(irreducibles, p -> apply(allPolys(d - deg p, R), G -> p*G))
)

randomPoly = method() -- returns a random monic polynomial of degree d
randomPoly (ZZ, PolynomialRing) := RingElement => (d, R) -> (R_0)^d + sum(d, i -> (random coefficientRing R)*(R_0)^i)

factorsOfDeg = method() -- returns all divisors of a polynomial of a specified degree
factorsOfDeg (ZZ, RingElement) := List => (d, F) -> (
	irredMults := (toList factor F)/toList;
	m := #irredMults;
	if m == 0 then return if d == deg F then {F} else {};
	a := getSymbol "a";
	T := QQ(monoid[a_1..a_m, Degrees => irredMults/first/deg]);
	Q := T/ideal apply(m, i -> T_i^(irredMults#i#1 + 1));
	flatten entries((map(ring F, T, matrix{irredMults/first})) sub(basis(d, Q), T))
)

quadraticSolver = method() -- solves a^2 + G*a = F (assumes all polynomials are monic)
quadraticSolver (RingElement, RingElement) := RingElement => (F, G) -> (
	if F == 0 then return F;
	(degF, degG) := (F, G)/deg;
	if degG > degF or 2*degG == degF or (odd degF and 2*degG < degF) then return null;
	d := if 2*degG > degF then degF - degG else degF//2;
	for a in factorsOfDeg(d, F) do if a*(a + G) == F then return a;
	-- for a in (toList factor F)/toList/(p -> toList(p#1:p#0))//flatten//subsets/product//unique do if a*(a + G) == F then return a;
)

sqrt RingElement := RingElement => F -> quadraticSolver(F, 0*F)

sqrt2 = f -> sum(exponents f, E -> (ring f)_(E//2))

rad = f -> if deg f <= 1 then f else sum(exponents f, E -> (ring f)_(E/(e -> if e == 0 then 0 else 1)))

squareFreePart = method()
squareFreePart RingElement := RingElement => F -> product((toList factor F)/toList, p -> p#0^(p#1 % 2))

------------------------------
-- Same orbit detection
------------------------------

minimalRepresentative = method()
minimalRepresentative (RingElement, RingElement, RingElement) := Sequence => (F, G, H) -> (
	msg := displayMessage_"minimalRepresentative";
	msg toString(G, H);
	(g, h) := (G, H)/deg;
	if (h > 2*g and odd h) or (h == 2*g) or (h < g) then (
		if h > 2*g then msg "type I"
		else if h == 2*g then msg "type II"
		else msg "type III";
		return (F, G, H)
	);
	x := (ring G)_0;
	n := if h > 2*g then h//2 else h - g;
	minimalRepresentative(F + x^n, G, H + G*x^n + x^(2*n))
)
minimalRepresentative (RingElement, RingElement) := Sequence => (G, H) -> minimalRepresentative(0_(ring G), G, H)

------------------------------
-- Brute-force search
------------------------------

needsPackage "SLPexpressions"

findPolySol = method()
findPolySol (ZZ, Ideal) := List => (d, I) -> (
	R := coefficientRing ring I;
	if char R == 0 then error "Expected finite prime field";
	n := #gens ring I;
	B := transpose basis(0,d,R);
	cand := sort apply(toList ((set(0..<char R)) ^** (numrows B) /deepSplice/toList), l -> (matrix{l}*B)_(0,0));
	C := set(0..<#cand);
	slp := makeSLProgram(gateMatrix{getVarGates ring I}, gateMatrix{I_*/gatePolynomial});
	(inp, out) := (mutableMatrix(R,1,n), mutableMatrix(R,1,1));
	sort for t in toList(C ^** n)/deepSplice/toList list (
		scan(n, i -> inp_(0,i) = cand#(t#i));
		evaluate(slp, inp, out);
		if out == 0 then first entries inp else continue
	)
)

------------------------------
-- Better search
------------------------------

fundamentalUnit = method(Options => {Degree => 80, Strategy => "MOD", symbol B0 => null, symbol Branches => {}, symbol ExactDegree => false}) -- Degree should be an upper bound (or range) for deg(B)
fundamentalUnit (RingElement, RingElement) := Sequence => opts -> (G, H) -> (
	msg := displayMessage_"fundamentalUnit";
	(F, G0, H0) := minimalRepresentative(G, H);
	(g, h) := (G, H0)/deg;
	if h > 2*g and odd h then return msg "type I minimal representative, unit group is trivial";
	R := ring G;
	if h == 2*g then (
		if g < 0 then ( msg "type II minimal representative with G = 0, unit group is (F_2[x],+)"; return (1 + F, 1_R) )
		else if g == 0 then ( msg "type II minimal representative with G = 1, unit group is ZZ/3"; return (F, 1_R) )
		else return msg "type II minimal representative, unit group is trivial";
	);
	if H0 == 0 then return msg "H0 = 0, unit group is trivial";
	if H0 == 1 then ( msg "H0 = 1"; return (F, 1_R) );
	if G % H0 == 0 then ( msg "H0 divides G"; return (1 + F*G//H0, G//H0) );
	B0list := if opts.B0 === null then {1_R} | subsets((toList factor G)/toList/first)/product - set{1,G} else {sub(opts.B0, R)};
	T := R(monoid(["U","V"]/getSymbol));
	(U,V) := toSequence gens T;
	(inp, out) := (mutableMatrix(R,1,2), mutableMatrix(R,1,1));
	degs := toList if instance(opts.Degree, ZZ) then 2*(g-h)..opts.Degree else opts.Degree; -- since B divides 1+A^2, deg(B) >= 2*(deg(G)-deg(H)) if A != 1
	D := ceiling((max degs)/2);
	(a,b) := ("a","b")/getSymbol;
	K := (ZZ/2)(monoid[a_0..a_(D-1),b_0..b_D]);
	A := K(monoid[gens R]);
	toA := map(A,R);
	if opts.ExactDegree then degs = {max degs};
	for d in degs do (
		for b0 in B0list do (
			degB0 := deg b0;
			if d < degB0 or odd(d - degB0) then continue;
			b1 := (d - degB0)//2;
			c := b1 + h - g;
			if c < 0 then continue;
			updateStatus("Searching for units in degree " | toString(d) | "...");
			Q := U^2 + U*V*G + V^2*H0 + (G // b0);
			if opts.Strategy === "BFS" then (
				slp := makeSLProgram(gateMatrix{getVarGates T}, gateMatrix{{gatePolynomial Q}});
				for C in allPolys(c, R) do (
					inp_(0,0) = C;
					for B1 in allPolys(b1, R) do (
						inp_(0,1) = B1;
						evaluate(slp, inp, out);
						if out == 0 then return (1 + b0*B1*(C + B1*F), b0*B1^2)
					)
				)
			) else if opts.Strategy === "DFS" then (
				u := iterativeSolver(Q, opts, B0 => b0, Degree => b1, ExactDegree => true);
				if u =!= null and u#1 != 0 then return (1 + b0*u#1*(u#0 + u#1*F), b0*u#1^2)
			) else (
				(C, B1) := (A_0^c + sum(c, i -> K_i*A_0^i), A_0^b1 + sum(b1, i -> K_(D+i)*A_0^i));
				Q = C^2 + C*B1*toA(G) + B1^2*toA(H0) + toA(G//b0);
				result := unitPolySystem(ideal sub(last coefficients Q, K), (D, c, b1), opts.Strategy);
				if result === null then continue;
				if instance(result, Ideal) then return result;
				u = (sub(C, result#0), B1)/(f -> sub(sub(f, result#1), R));
				return (1 + b0*u#1*(u#0 + u#1*F), b0*u#1^2)
			)
		)
	);
	msg("no units found in degree" | (if #degs > 1 then "s " else " ") | (if max degs - min degs + 1 == #degs and #degs > 1 then toString(min degs) | ".." | toString(max degs) else toString degs) | " (consider increasing Degree)");
)

iterativeSolver = method(Options => options fundamentalUnit) -- the optional input Branches should be a list of options of the form i => {coeff(x^i, c), coeff(x^i, b1), coeff(x^(i+1), c), coeff(x^(i+1), b1)}
iterativeSolver RingElement := Sequence => opts -> F -> (
	msg := displayMessage_"iterativeSolver";
	T := ring F;
	S := coefficientRing T;
	x := S_0;
	d := opts.Degree;
	branches := (if instance(opts.Branches, List) then hashTable else identity) opts.Branches;
	(U,V) := toSequence take(gens T, 2);
	(g,h) := (U*V, V^2)/(m -> deg coefficient(m, F));
	resPairs := {{0_T,0_T},{1_T,0_T},{0_T,1_T},{1_T,1_T}};
	candChoices := hashTable apply(d+1, i -> i => resPairs_(
		if opts.ExactDegree and i >= d - (g - h) - 1 then (
			if i == d - (g - h) - 1 then {1,3}
			else if i == d - 1 then {2}
			else if i == d then {0}
			else {0,2}
		) else {0,1,2,3}
	));
	evalZero := map(T, T, matrix{{0_T, 0_T}});
	resMaps := hashTable apply(resPairs, p -> p => map(T, T, matrix{{p#0 + x*U, p#1 + x*V}}));
	resMaps2 := hashTable flatten table(resPairs, resPairs, (p, q) -> (p, q) => map(T, T, matrix{{p#0 + x*q#0, p#1 + x*q#1}}));
	(Q,K,B) := (new MutableHashTable,new MutableHashTable,new MutableHashTable);
	Q#0 = F;
	i := 0;
	k0 := {null, null, null, null};
	doBacktrack := false;
	while true do (
		if i > d then (
			-- msg "Hit degree limit";
			doBacktrack = true;
		) else (
			validPairs := if k0#2 =!= null then {drop(k0, 2)} else resPairs;
			possibles := sort flatten for k in validPairs list (
				test := select(candChoices#i, l -> ((resMaps2#(k,l))(Q#i)) % (x^2) == 0);
				if #test == 4 then {k | {null,null}} else apply(test, l -> k | l)
			);
			if #possibles > 1 then (
				msg("Possible residues in degree " | net i | " from " | net k0 | ": " | net possibles);
				if branches#?i then (
					j := if instance(branches#i, ZZ) then branches#i else position(possibles, c -> all(#c, k -> c#k == branches#i#k));
					msg("Selecting branch " | net j | " at level " | net i);
					possibles = {possibles#j}; -- | possibles_(delete(j, toList(0..<#possibles)));
				) else B#i = 0;
			);
			if #possibles == 0 then doBacktrack = true else K#i = possibles;
		);
		if doBacktrack then (
			doBacktrack = false;
			branchPoints := select(keys K, k -> #K#k > 1);
			if #branchPoints == 0 then (
				msg("No branch points to backtrack to!");
				return;
			);
			-- msg("Backtrack level " | net i | " -> " | net max branchPoints);
			i = max branchPoints;
			K#i = drop(K#i, 1);
			B#i = B#i + 1;
			updateStatus(sort pairs B);
		);
		k0 = K#i#0;
		Q1 := (resMaps#(take(k0,2))) Q#i;
		while Q1 == x^2*(Q1//x^2) do Q1 = Q1//x^2;
		-- msg("New form: " | net Q1);
		Q#(i+1) = Q1;
		i = i+1;
		if (k0#2 === null or (k0#2 == 0 and k0#3 == 0)) and evalZero Q1 == 0 then (
			msg "Successful termination!";
			break
		);
	);
	msg net((Q, K)/pairs/hashTable);
	c := sum(i, j -> x^j*K#j#0#0);
	b1 := sum(i, j -> x^j*K#j#0#1);
	(c, b1)/(f -> sub(f, S))
)

unitPolySystem = method()
unitPolySystem (Ideal, Sequence, String) := Sequence => (I, consts, mode) -> (
	K := ring I;
	(D, c, b1) := consts;
	cValues := {};
	for i to c-1 do cValues = append(cValues, K_(c-1-i) => K_(c-1-i) + sub(I_i, cValues));
	J := sub(ideal drop(I_*, c), cValues);
	if mode === "EQS" then return J;
	J = simplifyEquations J; -- + ideal apply(b1, i -> K_(D+i)^2 - K_(D+i));
	(cValues, if mode === "MIN" then (
		-- J = J + ideal(K_(D+b1-1) + if minPres(J + ideal(K_(D+b1-1))) == 1 then 1 else 0);
		if minPres J == 1 then return;
		phi := J.cache#minimalPresentationMap.matrix;
		apply(b1, i -> K_(D+i) => sub(phi_(0,D+i),ZZ))
	) else (
		-- for i to b1-1 do J = trim(J + ideal(K_(D+b1-1-i) + if 1 % (J + ideal(K_(D+b1-1-i))) == 0 then 1 else 0));
		if 1 % J == 0 then return;
		apply(b1, i -> K_(D+i) => K_(D+i) % J)
	))
)

simplifyEquations = method() -- heuristic (partial) linearization
simplifyEquations Ideal := Ideal => I -> (
	S := support I;
	equations := {I_0};
	for i from 1 to #I_*-1 do equations = append(equations, rad(I_i + (
		sum(min(i, #S), j -> equations#(i-j-1)*S#(-j-1))
	)));
	ideal equations
)
simplifyEquations (RingElement, RingElement, ZZ) := Ideal => (G, H, d) -> simplifyEquations fundamentalUnit(G, H, Degree => {d}, Strategy => "EQS")

-- TODO:
-- Handle x -> x+1 automorphism

end--

-- Brute-force example
S = ZZ/2[x]
R = S[a,b]
(g,h) = (x^2,x+1)
F = a^2 + a*b*g + b^2*h + 1
elapsedTime findPolySol(6, ideal F)

L = allPolys(3, S)
elapsedTime H = hashTable flatten table(L, L, (g,h) -> elapsedTime (g,h) => findPolySol(6, ideal(a^2 + a*b*g + b^2*h + 1)));
select(keys H, k -> #H#k == 1)

-- fundamentalUnit examples
(G,H) = (x^2+x+1,x)
(G,H) = (x^3+x^2+1,x^2)
(G,H) = (x^2,x+1) -- maximal deg fundamental unit with deg(G) <= 2
(G,H) = (x^3,x+1)
(G,H) = (x^3+1,x)
(G,H) = (x^3,x^2+1) -- achieves minimal degree for B, i.e. 2*(deg(G) - deg(H))
(G,H) = (x^3+x,x^2+x+1) -- true B0 is x*(x+1), though BFS finds deg 15 solution with B0=>x
(G,H) = (x^3+x^2+1, x^2+x) -- maximal deg fundamental unit with deg(G) <= 3

(G, H) = (randomPoly(3, S), randomPoly(8, S))
(G, H) = (randomPoly(4, S), randomPoly(7, S))
minimalRepresentative(G, H)

elapsedTime fundamentalUnit(G, H, Strategy => "MOD")
elapsedTime fundamentalUnit(G, H, Strategy => "MIN", Degree => {33})
elapsedTime fundamentalUnit(G, H, Strategy => "MOD", Degree => {84})

elapsedTime fundamentalUnit(G, H, Strategy => "BFS")
elapsedTime fundamentalUnit(G, H, Strategy => "BFS", Degree => 20)
elapsedTime fundamentalUnit(G, H, Strategy => "BFS", Degree => 17..20)
elapsedTime fundamentalUnit(G, H, Strategy => "BFS", Degree => {16})
elapsedTime fundamentalUnit(G, H, Strategy => "BFS", B0 => sqrt G, Degree => {20})
(a,b) = oo; a^2 + a*b*G + b^2*H == 1
(b0,b1) = (squareFreePart b, sqrt(b//squareFreePart b))
c = (a+1)//(b0*b1)

elapsedTime fundamentalUnit(G, H)
elapsedTime fundamentalUnit(G, H, B0 => 1)
elapsedTime fundamentalUnit(G, H, B0 => S_0)
elapsedTime fundamentalUnit(G, H, Degree => 20)
elapsedTime fundamentalUnit(G, H, Degree => {52})
elapsedTime fundamentalUnit(x^3+x^2+1, x^2+x, Strategy => "DFS", Branches => {0 => {1,0,1,0}, 2 => {1,0,0,1}, 4 => {1,0,0,0}, 6 => {0,0,1,0}}) -- Branches => {0=>1,2=>2,4=>2}
elapsedTime fundamentalUnit(G, H, B0 => x, Strategy => "DFS", Branches => {5=>4}, Degree => 33, ExactDegree => true)
elapsedTime fundamentalUnit(G, H, Branches => {0=>1}, Degree => 42, ExactDegree => true)

R = S[y]
T = R/ideal(y^2 + sub(G,R)*y + sub(H,R))
u = sub(a,T) + sub(b,T)*y
toSequence reverse flatten entries last coefficients(u^2)

psi = map(S,S,{x => x+1})
L = apply(toList(1..6), i -> allPolys(i, S));
checkedPairs = new MutableHashTable
for G in L#-1 do for H in flatten drop(L, -1) do if not checkedPairs#?(psi G, psi H) then checkedPairs#(G,H) = 1
scan(keys checkedPairs, k -> if k#0 % k#1 == 0 then remove(checkedPairs, k))
#keys checkedPairs
elapsedTime for k in keys checkedPairs do elapsedTime if checkedPairs#k == 1 then checkedPairs#k = fundamentalUnit(k#0,k#1,Degree=>40)
hashTable pairs checkedPairs

-- High degree fundamental units
-- Deg 20
(G,H) = (x^4+x^2+1,x) -- B0 => x^2+x+1, Branches => {0=>1,2=>1}

-- Deg 21
(G,H) = (x^4+x^3+x^2,x+1) -- B0 => x*(x^2+x+1), Branches => {2=>2}

-- Deg 22
(G,H) = (x^4+x^3+1,x^2) -- Branches => {2=>2,4=>2,6=>1}
(G,H) = (x^4+x^3+x^2+x+1,x^3+1) -- Branches => {0=>4,2=>1,4=>3,8=>3}
(G,H) = (x^4+x+1,x^3+1) -- Branches => {4=>2,6=>1,8=>1}
(G,H) = (x^4+x+1,x^3) -- Branches => {0=>1,8=>1}

-- Deg 23
(G,H) = (x^4+x^2+x,x+1) -- B0 => x, Branches => {1=>2,3=>2}
(G,H) = (x^4,x^2+x) -- B0 => x, Branches => {5=>2,7=>3}
(G,H) = (x^4+x^3+x,x^3+x^2) -- B0 => x, Branches => {1=>1,3=>3,5=>3,7=>2}

-- Deg 24
(G,H) = (x^4+x^3+1,x^3+1) -- Branches => {2=>2,4=>3,6=>1,8=>3}

-- Deg 29
(G,H) = (x^4+x^2+x,x^3+x^2) -- B0 => x, Branches => {1=>1,3=>2,5=>3,7=>1,9=>3}

-- Deg 33
(G,H) = (x^4, x+1) -- B0 => x, Branches => {5=>4,7=>2,9=>1,11=>2}
-- Note: with Degree => 20, iterativeSolver finds the inverse fundamental unit first
(G,H) = (x^4,x^3+x) -- B0 => x, Branches => {5=>4,7=>2,9=>3,11=>3}

-- Deg 36
(G,H) = (x^5,x+1)

-- Deg 42
(G,H) = (x^4+x^3+1,x^3+x^2) -- Branches => {2=>3,8=>1,12=>2,14=>3,16=>2}
(G,H) = (x^4+x^3+1,x^2+x) -- Branches => {0=>1,8=>2,10=>3,14=>2,16=>2}
(G,H) = (x^4+x+1,x^3+x) -- Branches => {0=>1,2=>1,4=>2,6=>1,8=>1,10=>2}

-- Deg 48
(G,H) = (x^4+x^2+1,x^3+x) -- B0 => sqrt G, Branches => {0=>1,4=>3,6=>1,8=>2,10=>1,12=>3}

-- Deg 52
(G,H) = (x^4+x^3+1,x^3+x) -- maximal deg fundamental unit with deg(G) <= 4

-- Deg 61
(G,H) = (x^5+x^3+x,x^4+x^2+x+1)

-- Deg 67
(G,H) = (x^5+x^3+x,x^3+x^2)

-- Deg 73
(G,H) = (x^5+x^2+x,x^4+x^3+x+1)
(G,H) = (x^5+x^2+x,x+1)
(G,H) = (x^5+x^3+x+1,x^4+x^3+x^2)

-- Deg 76
(G,H) = (x^5,x^4+x^3+x+1)
(G,H) = (x^5,x^4+x^3+x^2+x)

-- Deg 79
(G,H) = (x^6,x+1)
(G,H) = (x^5+1,x^4+x^2+x)

-- Deg 84
(G,H) = (x^5+x^3+1,x^4+x^2)
(G,H) = (x^5+x^3+x^2+x+1,x^3+x^2)
(G,H) = (x^5+x^2+1,x^3+x^2)

-- Deg 86
(G,H) = (x^5,x^4+x^2+x+1) -- B0 => 1

-- Deg 90
(G,H) = (x^5+x+1,x^4+x^3+x^2+x) -- B0 => x^2+x+1

-- Deg 94
(G,H) = (x^5+x^3+x^2+x+1,x^2+x)
(G,H) = (x^5+x^2+1,x^4+x^3+x^2+x)

-- Deg 96
(G,H) = (x^5+x^3+x^2+x+1,x^4+x^3+x^2+x)
(G,H) = (x^5+x^3+1,x^4+x^3)
(G,H) = (x^5+x^2+1,x^3+x)

-- Deg 106
(G,H) = (x^5+x^3+1,x^3+x)
(G,H) = (x^5+x^2+1,x^4+x^3)

-- Deg 124
(G,H) = (x^5+x^3+x^2+x+1,x^4+x^3)
(G,H) = (x^5+x^3+1,x^4+x^3+x^2+x)

-- Deg 132
(G,H) = (x^5+x^3+x^2+x+1,x^3+x)
(G,H) = (x^5+x^3+1,x^4+x)
(G,H) = (x^5+x^2+1,x^4+x)

-- Deg 134
(G,H) = (x^5+x^2+1,x^2+x)
(G,H) = (x^5+x^3+x^2+x+1,x^4+x)
(G,H) = (x^5+x^3+1,x^3+x^2)

-- Deg 378
(G,H) = (x^7,x+1)

-- Case study: (G,H) = (x^n, x+1)
n = 4
d = 33
(a,b) = fundamentalUnit(x^n, x+1, B0 => x^((n-1)%2), Degree => {d})/(f -> matrix entries last coefficients(f, Monomials => basis(0, deg f, S)))
F = S^(d+1)
b0 = i -> if i > d then 0*F^{0} else F^{i}
A = matrix apply(d+2-n, i -> {sum(d, j -> b0(i+(2^(j+1)-1)*n - 2^j) + b0(i+(2^(j+1)-1)*n))})
-- A == matrix table(d+2-n,d+1, (i,j) -> if member(j - i - (n-1), {0,1,7,9,21,25}) then 1_S else 0)
A*b == a
Ainv = inverse submatrix'(A, toList(0..<n-1))
Ainv * a == submatrix'(b, toList(0..<n-1), )

restart
load "UnitsHyperellipticCurves.m2"
debugLevel = 1
S = ZZ/2[x]
