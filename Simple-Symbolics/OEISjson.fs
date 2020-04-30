﻿module OEISjson

[<Literal>]
let json = """
{
	"greeting": "Greetings from The On-Line Encyclopedia of Integer Sequences! http://oeis.org/",
	"query": "1,2,3,4",
	"count": 10879,
	"start": 0,
	"results": [
		{
			"number": 27,
			"id": "M0472 N0173",
			"data": "1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77",
			"name": "The positive integers. Also called the natural numbers, the whole numbers or the counting numbers, but these terms are ambiguous.",
			"comment": [
				"For some authors, the terms \"natural numbers\" and \"counting numbers\" include 0, i.e., refer to the nonnegative integers A001477; the term \"whole numbers\" frequently also designates the whole set of (signed) integers A001057.",
				"a(n) is smallest positive integer which is consistent with sequence being monotonically increasing and satisfying a(a(n)) = n (cf. A007378).",
				"Inverse Euler transform of A000219.",
				"The rectangular array having A000027 as antidiagonals is the dispersion of the complement of the triangular numbers, A000217 (which triangularly form column 1 of this array). The array is also the transpose of A038722. - _Clark Kimberling_, Apr 05 2003",
				"For nonzero x, define f(n) = floor(nx) - floor(n/x). Then f=A000027 if and only if x=tau or x=-tau. - _Clark Kimberling_, Jan 09 2005",
				"Numbers of form (2^i)*k for odd k (i.e., n = A006519(n)*A000265(n)); thus n corresponds uniquely to an ordered pair (i,k) where i=A007814, k=A000265 (with A007814(2n)=A001511(n), A007814(2n+1)=0). - _Lekraj Beedassy_, Apr 22 2006",
				"If the offset were changed to 0, we would have the following pattern: a(n)=binomial(n,0) + binomial(n,1) for the present sequence (number of regions in 1-space defined by n points), A000124 (number of regions in 2-space defined by n straight lines), A000125 (number of regions in 3-space defined by n planes), A000127 (number of regions in 4-space defined by n hyperplanes), A006261, A008859, A008860, A008861, A008862 and A008863, where the last six sequences are interpreted analogously and in each \"... by n ...\" clause an offset of 0 has been assumed, resulting in a(0)=1 for all of them, which corresponds to the case of not cutting with a hyperplane at all and therefore having one region. - Peter C. Heinig (algorithms(AT)gmx.de), Oct 19 2006",
				"Define a number of points on a straight line to be in general arrangement when no two points coincide. Then these are the numbers of regions defined by n points in general arrangement on a straight line, when an offset of 0 is assumed. For instance, a(0)=1, since using no point at all leaves one region. The sequence satisfies the recursion a(n) = a(n-1) + 1. This has the following geometrical interpretation: Suppose there are already n-1 points in general arrangement, thus defining the maximal number of regions on a straight line obtainable by n-1 points, and now one more point is added in general arrangement. Then it will coincide with no other point and act as a dividing wall thereby creating one new region in addition to the a(n-1)=(n-1)+1=n regions already there, hence a(n)=a(n-1)+1. Cf. the comments on A000124 for an analogous interpretation. - Peter C. Heinig (algorithms(AT)gmx.de), Oct 19 2006",
				"The sequence a(n)=n (for n=1,2,3) and a(n)=n+1 (for n=4,5,...) gives to the rank (minimal cardinality of a generating set) for the semigroup I_n\\S_n, where I_n and S_n denote the symmetric inverse semigroup and symmetric group on [n]. - _James East_, May 03 2007",
				"The sequence a(n)=n (for n=1,2), a(n)=n+1 (for n=3) and a(n)=n+2 (for n=4,5,...) gives the rank (minimal cardinality of a generating set) for the semigroup PT_n\\T_n, where PT_n and T_n denote the partial transformation semigroup and transformation semigroup on [n]. - _James East_, May 03 2007",
				"\"God made the integers; all else is the work of man.\" This famous quotation is a translation of \"Die ganzen Zahlen hat der liebe Gott gemacht, alles andere ist Menschenwerk,\" spoken by Leopold Kronecker in a lecture at the Berliner Naturforscher-Versammlung in 1886. Possibly the first publication of the statement is in Heinrich Weber's \"Leopold Kronecker,\" Jahresberichte D.M.V. 2 (1893) 5-31. - _Clark Kimberling_, Jul 07 2007",
				"Binomial transform of A019590, inverse binomial transform of A001792. - _Philippe Deléham_, Oct 24 2007",
				"Writing A000027 as N, perhaps the simplest one-to-one correspondence between N X N and N is this: f(m,n) = ((m+n)^2 - m - 3n + 2)/2. Its inverse is given by I(k)=(g,h), where g = k - J(J-1)/2, h = J + 1 - g, J = floor((1 + sqrt(8k - 7))/2). Thus I(1)=(1,1), I(2)=(1,2), I(3)=(2,1) and so on; the mapping I fills the first-quadrant lattice by successive antidiagonals. - _Clark Kimberling_, Sep 11 2008",
				"A000007(a(n)) = 0; A057427(a(n)) = 1. - _Reinhard Zumkeller_, Oct 12 2008",
				"a(n) is also the mean of the first n odd integers. - _Ian Kent_, Dec 23 2008",
				"Equals INVERTi transform of A001906, the even-indexed Fibonacci numbers starting (1, 3, 8, 21, 55, ...). - _Gary W. Adamson_, Jun 05 2009",
				"These are also the 2-rough numbers: positive integers that have no prime factors less than 2. - _Michael B. Porter_, Oct 08 2009",
				"Totally multiplicative sequence with a(p) = p for prime p. Totally multiplicative sequence with a(p) = a(p-1) + 1 for prime p. - _Jaroslav Krizek_, Oct 18 2009",
				"Triangle T(k,j) of natural numbers, read by rows, with T(k,j) = binomial(k,2) + j = (k^2-k)/2 + j where 1\u003c=j\u003c=k. In other words, a(n) = n = binomial(k,2) + j where k is the largest integer such that binomial(k,2) \u003c n and j = n - binomial(k,2). For example, T(4,1)=7, T(4,2)=8, T(4,3)=9, and T(4,4)=10. Note that T(n,n)=A000217(n), the n-th triangular number. - _Dennis P. Walsh_, Nov 19 2009",
				"Hofstadter-Conway-like sequence (see A004001): a(n) = a(a(n-1)) + a(n-a(n-1)) with a(1) = 1, a(2) = 2. - _Jaroslav Krizek_, Dec 11 2009",
				"a(n) is also the dimension of the irreducible representations of the Lie algebra sl(2). - _Leonid Bedratyuk_, Jan 04 2010",
				"Floyd's triangle read by rows. - _Paul Muljadi_, Jan 25 2010",
				"Number of numbers between k and 2k where k is an integer. - _Giovanni Teofilatto_, Mar 26 2010",
				"Generated from a(2n) = r*a(n), a(2n+1) = a(n) + a(n+1), r = 2; in an infinite set, row 2 of the array shown in A178568. - _Gary W. Adamson_, May 29 2010",
				"1/n = continued fraction [n]. Let barover[n] = [n,n,n,...] = 1/k. Then k - 1/k = n. Example: [2,2,2,...] = (sqrt(2) - 1) = 1/k, with k = (sqrt(2) + 1). Then 2 = k - 1/k. - _Gary W. Adamson_, Jul 15 2010",
				"Number of n-digit numbers the binary expansion of which contains one run of 1's. - _Vladimir Shevelev_, Jul 30 2010",
				"From _Clark Kimberling_, Jan 29 2011: (Start)",
				"Let T denote the \"natural number array A000027\":",
				"   1    2    4    7 ...",
				"   3    5    8   12 ...",
				"   6    9   13   18 ...",
				"  10   14   19   25 ...",
				"T(n,k) = n+(n+k-2)*(n+k-1)/2. See A185787 for a list of sequences based on T, such as rows, columns, diagonals, and sub-arrays. (End)",
				"The Stern polynomial B(n,x) evaluated at x=2. See A125184. - _T. D. Noe_, Feb 28 2011",
				"The denominator in the Maclaurin series of log(2), which is 1 - 1/2 + 1/3 - 1/4 + .... - _Mohammad K. Azarian_, Oct 13 2011",
				"As a function of Bernoulli numbers B_n (cf. A027641: (1, -1/2, 1/6, 0, -1/30, 0, 1/42, ...)): let V = a variant of B_n changing the (-1/2) to (1/2). Then triangle A074909 (the beheaded Pascal's triangle) * [1, 1/2, 1/6, 0, -1/30, ...] = the vector [1, 2, 3, 4, 5, ...]. - _Gary W. Adamson_, Mar 05 2012",
				"Number of partitions of 2n+1 into exactly two parts. - _Wesley Ivan Hurt_, Jul 15 2013",
				"Integers n dividing u(n) = 2u(n-1) - u(n-2); u(0)=0, u(1)=1 (Lucas sequence A001477). - _Thomas M. Bridge_, Nov 03 2013",
				"For this sequence, the generalized continued fraction a(1)+a(1)/(a(2)+a(2)/(a(3)+a(3)/(a(4)+...))), evaluates to 1/(e-2) = A194807. - _Stanislav Sykora_, Jan 20 2014",
				"Engel expansion of e-1 (A091131 = 1.71828...). - _Jaroslav Krizek_, Jan 23 2014",
				"a(n) is the number of permutations of length n simultaneously avoiding 213, 231 and 321 in the classical sense which are breadth-first search reading words of increasing unary-binary trees. For more details, see the entry for permutations avoiding 231 at A245898. - _Manda Riehl_, Aug 05 2014",
				"a(n) is also the number of permutations simultaneously avoiding 213, 231 and 321 in the classical sense which can be realized as labels on an increasing strict binary tree with 2n-1 nodes. See A245904 for more information on increasing strict binary trees. - _Manda Riehl_ Aug 07 2014",
				"a(n) = least k such that 2*Pi - Sum_{h=1..k} 1/(h^2 - h + 3/16) \u003c 1/n. - _Clark Kimberling_, Sep 28 2014",
				"a(n) = least k such that Pi^2/6 - Sum_{h=1..k} 1/h^2 \u003c 1/n. - _Clark Kimberling_, Oct 02 2014",
				"Determinants of the spiral knots S(2,k,(1)). a(k) = det(S(2,k,(1))). These knots are also the torus knots T(2,k). - _Ryan Stees_, Dec 15 2014",
				"As a function, the restriction of the identity map on the nonnegative integers {0,1,2,3...}, A001477, to the positive integers {1,2,3,...}. - _M. F. Hasler_, Jan 18 2015",
				"See also A131685(k) = smallest positive number m such that c(i) = m (i^1 + 1) (i^2 + 2) ... (i^k+ k) / k! takes integral values for all i\u003e=0: For k=1, A131685(k)=1, which implies that this is a well defined integer sequence. - _Alexander R. Povolotsky_, Apr 24 2015",
				"a(n) is the number of compositions of n+2 into n parts avoiding the part 2. - _Milan Janjic_, Jan 07 2016",
				"Does not satisfy Benford's law [Berger-Hill, 2017] - _N. J. A. Sloane_, Feb 07 2017",
				"Parametrization for the finite multisubsets of the positive integers, where, for p_j the j-th prime, n = Prod_j p_j^{e_j} corresponds to the multiset containing e_j copies of j ('Heinz encoding' -- see A056239, A003963, A289506, A289507, A289508, A289509) - _Christopher J. Smyth_, Jul 31 2017",
				"The arithmetic function v_1(n,1) as defined in A289197. - _Robert Price_, Aug 22 2017",
				"For n\u003e=3, a(n)=n is the least area that can be obtained for an irregular octagon drawn in a square of n units side, whose sides are parallel to the axes, with 4 vertices that coincide with the 4 vertices of the square, and the 4 remaining vertices having integer coordinates. See Affaire de Logique link. - _Michel Marcus_, Apr 28 2018",
				"a(n+1) is the order of rowmotion on a poset defined by a disjoint union of chains of length n. - _Nick Mayers_, Jun 08 2018",
				"Number of 1's in n-th generation of 1-D Cellular Automata using Rules 50, 58, 114, 122, 178, 186, 206, 220, 238, 242, 250 or 252 in the Wolfram numbering scheme, started with a single 1. - _Frank Hollstein_, Mar 25 2019",
				"(1, 2, 3, 4, 5,...) is the fourth INVERT transform of (1, -2, 3, -4, 5,...). - Gary W. Adamson_, Jul 15 2019"
			],
			"reference": [
				"T. M. Apostol, Introduction to Analytic Number Theory, Springer-Verlag, 1976, page 1.",
				"T. M. Apostol, Modular Functions and Dirichlet Series in Number Theory, Springer-Verlag, 1990, page 25.",
				"W. Fulton and J. Harris, Representation theory: a first course, (1991), page 149. [From _Leonid Bedratyuk_, Jan 04 2010]",
				"I. S. Gradstein and I. M. Ryshik, Tables of series, products , and integrals, Volume 1, Verlag Harri Deutsch, 1981.",
				"R. E. Schwartz, You Can Count on Monsters: The First 100 numbers and Their Characters, A. K. Peters and MAA, 2010.",
				"N. J. A. Sloane, A Handbook of Integer Sequences, Academic Press, 1973 (includes this sequence).",
				"N. J. A. Sloane and Simon Plouffe, The Encyclopedia of Integer Sequences, Academic Press, 1995 (includes this sequence)."
			],
			"link": [
				"N. J. A. Sloane, \u003ca href=\"/A000027/b000027.txt\"\u003eTable of n, a(n) for n = 1..500000\u003c/a\u003e [a large file]",
				"Archimedes Laboratory, \u003ca href=\"http://www.archimedes-lab.org/numbers/Num1_200.html\"\u003eWhat's special about this number?\u003c/a\u003e",
				"Affaire de Logique, \u003ca href=\"http://www.affairedelogique.com/espace_probleme.php?corps=probleme\u0026amp;num=1051\"\u003ePick et Pick et Colegram\u003c/a\u003e (in French), No. 1051, 18-04-2018.",
				"Paul Barry, \u003ca href=\"http://www.cs.uwaterloo.ca/journals/JIS/VOL8/Barry/barry84.html\"\u003eA Catalan Transform and Related Transformations on Integer Sequences\u003c/a\u003e, Journal of Integer Sequences, Vol. 8 (2005), Article 05.4.5.",
				"James Barton, \u003ca href=\"http://www.virtuescience.com/number-list.html\"\u003eThe Numbers\u003c/a\u003e",
				"A. Berger and T. P. Hill, \u003ca href=\"http://www.ams.org/publications/journals/notices/201702/rnoti-p132.pdf\"\u003eWhat is Benford's Law?\u003c/a\u003e, Notices, Amer. Math. Soc., 64:2 (2017), 132-134.",
				"A. Breiland, L. Oesper, and L. Taalman, \u003ca href=\"http://educ.jmu.edu/~taalmala/breil_oesp_taal.pdf\"\u003ep-Coloring classes of torus knots\u003c/a\u003e, Online Missouri J. Math. Sci., 21 (2009), 120-126.",
				"N. Brothers, S. Evans, L. Taalman, L. Van Wyk, D. Witczak, and C. Yarnall, \u003ca href=\"http://projecteuclid.org/euclid.mjms/1312232716\"\u003eSpiral knots\u003c/a\u003e, Missouri J. of Math. Sci., 22 (2010).",
				"C. K. Caldwell, \u003ca href=\"http://primes.utm.edu/curios\"\u003ePrime Curios\u003c/a\u003e",
				"Case and Abiessu, \u003ca href=\"http://everything2.net/index.pl?node_id=17633\u0026amp;displaytype=printable\u0026amp;lastnode_id=17633\"\u003einteresting number\u003c/a\u003e",
				"S. Crandall, \u003ca href=\"http://tingilinde.typepad.com/starstuff/2005/11/significant_int.html\"\u003enotes on interesting digital ephemera\u003c/a\u003e",
				"O. Curtis, \u003ca href=\"http://users.pipeline.com.au/owen/Numbers.html\"\u003eInteresting Numbers\u003c/a\u003e",
				"M. DeLong, M. Russell, and J. Schrock, \u003ca href=\"http://dx.doi.org/10.2140/involve.2015.8.361\"\u003eColorability and determinants of T(m,n,r,s) twisted torus knots for n equiv. +/-1(mod m)\u003c/a\u003e, Involve, Vol. 8 (2015), No. 3, 361-384.",
				"Walter Felscher, \u003ca href=\"http://sunsite.utk.edu/math_archives/.http/hypermail/historia/may99/0210.html\"\u003eHistoria Matematica Mailing List Archive.\u003c/a\u003e",
				"P. Flajolet and R. Sedgewick, \u003ca href=\"http://algo.inria.fr/flajolet/Publications/books.html\"\u003eAnalytic Combinatorics\u003c/a\u003e, 2009; see page 371",
				"Robert R. Forslund, \u003ca href=\"http://www.emis.de/journals/SWJPAM/Vol1_1995/rrf01.ps\"\u003eA logical alternative to the existing positional number system\u003c/a\u003e, Southwest Journal of Pure and Applied Mathematics, Vol. 1 1995 pp. 27-29.",
				"E. Friedman, \u003ca href=\"http://www.stetson.edu/~efriedma/numbers.html\"\u003eWhat's Special About This Number?\u003c/a\u003e",
				"R. K. Guy, \u003ca href=\"/A000346/a000346.pdf\"\u003eLetter to N. J. A. Sloane\u003c/a\u003e",
				"Milan Janjic, \u003ca href=\"http://www.pmfbl.org/janjic/\"\u003eEnumerative Formulas for Some Functions on Finite Sets\u003c/a\u003e",
				"Kival Ngaokrajang, \u003ca href=\"/A000027/a000027_2.pdf\"\u003eIllustration about relation to many other sequences\u003c/a\u003e, when the sequence is considered as a triangular table read by its antidiagonals. \u003ca href=\"/A000027/a000027_3.pdf\"\u003eAdditional illustrations\u003c/a\u003e when the sequence is considered as a centered triangular table read by rows.",
				"M. Keith, \u003ca href=\"http://users.aol.com/s6sj7gt/interest.htm\"\u003eAll Numbers Are Interesting: A Constructive Approach\u003c/a\u003e",
				"Leonardo of Pisa [Leonardo Pisano], \u003ca href=\"/A000027/a000027.jpg\"\u003eIllustration of initial terms\u003c/a\u003e, from Liber Abaci [The Book of Calculation], 1202 (photo by David Singmaster).",
				"R. Munafo, \u003ca href=\"http://www.mrob.com/pub/math/numbers.html\"\u003eNotable Properties of Specific Numbers\u003c/a\u003e",
				"G. Pfeiffer, \u003ca href=\"http://www.cs.uwaterloo.ca/journals/JIS/VOL7/Pfeiffer/pfeiffer6.html\"\u003eCounting Transitive Relations\u003c/a\u003e, Journal of Integer Sequences, Vol. 7 (2004), Article 04.3.2.",
				"R. Phillips, \u003ca href=\"http://richardphillips.org.uk/number/Num1.htm\"\u003eNumbers from one to thirty-one\u003c/a\u003e",
				"J. Striker, \u003ca href=\"http://www.ams.org/publications/journals/notices/201706/rnoti-p543.pdf\"\u003eDynamical Algebraic Combinatorics: Promotion, Rowmotion, and Resonance\u003c/a\u003e, Notices of the AMS, June/July 2017, pp. 543-549.",
				"G. Villemin's Almanac of Numbers, \u003ca href=\"http://villemin.gerard.free.fr/aNombre/Nb0a50.htm\"\u003eNOMBRES en BREF (in French)\u003c/a\u003e",
				"Eric Weisstein's World of Mathematics, \u003ca href=\"http://mathworld.wolfram.com/NaturalNumber.html\"\u003eNatural Number\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/PositiveInteger.html\"\u003ePositive Integer\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/CountingNumber.html\"\u003eCounting Number\u003c/a\u003e \u003ca href=\"http://mathworld.wolfram.com/Composition.html\"\u003eComposition\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/Davenport-SchinzelSequence.html\"\u003eDavenport-Schinzel Sequence\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/IdempotentNumber.html\"\u003eIdempotent Number\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/N.html\"\u003eN\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/SmarandacheCeilFunction.html\"\u003eSmarandache Ceil Function\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/WholeNumber.html\"\u003eWhole Number\u003c/a\u003e, \u003ca href=\"http://mathworld.wolfram.com/EngelExpansion.html\"\u003eEngel Expansion\u003c/a\u003e, and \u003ca href=\"http://mathworld.wolfram.com/TrinomialCoefficient.html\"\u003eTrinomial Coefficient\u003c/a\u003e",
				"Wikipedia, \u003ca href=\"http://en.wikipedia.org/wiki/List_of_numbers\"\u003eList of numbers\u003c/a\u003e, \u003ca href=\"http://en.wikipedia.org/wiki/Interesting_number_paradox\"\u003eInteresting number paradox\u003c/a\u003e, and \u003ca href=\"http://en.wikipedia.org/wiki/Floyd%27s_triangle\"\u003eFloyd's triangle\u003c/a\u003e",
				"Robert G. Wilson v, \u003ca href=\"/A000027/a000027.txt\"\u003eEnglish names for the numbers from 0 to 11159 without spaces or hyphens \u003c/a\u003e",
				"Robert G. Wilson v, \u003ca href=\"/A001477/a001477.txt\"\u003eAmerican English names for the numbers from 0 to 100999 without spaces or hyphens\u003c/a\u003e",
				"\u003ca href=\"/index/Cor#core\"\u003eIndex entries for \"core\" sequences\u003c/a\u003e",
				"\u003ca href=\"/index/Aa#aan\"\u003eIndex entries for sequences of the a(a(n)) = 2n family\u003c/a\u003e",
				"\u003ca href=\"/index/Per#IntegerPermutation\"\u003eIndex entries for sequences that are permutations of the natural numbers\u003c/a\u003e",
				"\u003ca href=\"/index/Par#partN\"\u003eIndex entries for related partition-counting sequences\u003c/a\u003e",
				"\u003ca href=\"/index/Rec#order_02\"\u003eIndex entries for linear recurrences with constant coefficients\u003c/a\u003e, signature (2,-1).",
				"\u003ca href=\"/index/Di#divseq\"\u003eIndex to divisibility sequences\u003c/a\u003e",
				"\u003ca href=\"/index/Be#Benford\"\u003eIndex entries for sequences related to Benford's law\u003c/a\u003e"
			],
			"formula": [
				"a(2k+1) = A005408(k), k \u003e= 0, a(2k) = A005843(k), k \u003e= 1.",
				"Multiplicative with a(p^e) = p^e. - _David W. Wilson_, Aug 01 2001",
				"Another g.f.: Sum_{n\u003e0} phi(n)*x^n/(1-x^n) (Apostol).",
				"When seen as an array: T(k, n) = n+1 + (k+n)*(k+n+1)/2. Main diagonal is 2n*(n+1)+1 (A001844), antidiagonal sums are n*(n^2+1)/2 (A006003). - _Ralf Stephan_, Oct 17 2004",
				"Dirichlet generating function: zeta(s-1). - _Franklin T. Adams-Watters_, Sep 11 2005",
				"G.f.: x/(1-x)^2. E.g.f.: x*exp(x). a(n)=n. a(-n)=-a(n).",
				"Series reversion of g.f. A(x) is x*C(-x)^2 where C(x) is the g.f. of A000108. - _Michael Somos_, Sep 04 2006",
				"G.f. A(x) satisfies 0 = f(A(x), A(x^2)) where f(u, v) = u^2 - v - 4*u*v. - _Michael Somos_, Oct 03 2006",
				"Convolution of A000012 (the all-ones sequence) with itself. - _Tanya Khovanova_, Jun 22 2007",
				"a(n) = 2*a(n-1)-a(n-2); a(1)=1, a(2)=2. a(n)=1+a(n-1). - _Philippe Deléham_, Nov 03 2008",
				"a(n) = A000720(A000040(n)). - _Juri-Stepan Gerasimov_, Nov 29 2009",
				"a(n+1) = Sum_{k=0..n} A101950(n,k). - _Philippe Deléham_, Feb 10 2012",
				"a(n) = Sum_{d | n} phi(d) = Sum_{d | n} A000010(d). - _Jaroslav Krizek_, Apr 20 2012",
				"G.f.: x * Product_{j\u003e=0} (1+x^(2^j))^2 = x * (1+2*x+x^2) * (1+2*x^2+x^4) * (1+2*x^4+x^8) * ... = x + 2x^2 + 3x^3 + ... . - _Gary W. Adamson_, Jun 26 2012",
				"a(n) = det(binomial(i+1,j), 1 \u003c= i,j \u003c= n). - _Mircea Merca_, Apr 06 2013",
				"E.g.f.: x*E(0), where E(k)= 1 + 1/(x - x^3/(x^2 + (k+1)/E(k+1) )); (continued fraction). - _Sergei N. Gladkovskii_, Aug 03 2013",
				"From _Wolfdieter Lang_, Oct 09 2013: (Start)",
				"a(n) = Product_{k=1..n-1} 2*sin(Pi*k/n), n \u003e 1.",
				"a(n) = Product_{k=1..n-1} (2*sin(Pi*k/(2*n)))^2, n \u003e 1.",
				"These identities are used in the calculation of products of length ratios of certain lines in a regular n-gon. For the first identity see the Gradstein-Ryshik reference, p. 62, 1.392 1., bringing the first factor there to the left hand side and taking the limit x -\u003e 0 (L'Hôpital). The second line follows from the first one. Thanks to _Seppo Mustonen_ who led me to consider n-gon lengths products. (End)",
				"a(n) = Sum_{j=0..k} (-1)^(j-1)*j*binomial(n,j)*binomial(n-1+k-j,k-j), k\u003e=0. - _Mircea Merca_, Jan 25 2014",
				"a(n) = A052410(n)^A052409(n). - _Reinhard Zumkeller_, Apr 06 2014",
				"a(n) = Sum_{k=1..n^2+2*n} 1/(sqrt(k)+sqrt(k+1)). - _Pierre CAMI_, Apr 25 2014",
				"a(n) = floor(1/sin(1/n)) = floor(cot(1/(n+1))) = ceiling(cot(1/n)). - _Clark Kimberling_, Oct 08 2014",
				"a(n) = floor(1/(log(n+1)-log(n))). - _Thomas Ordowski_, Oct 10 2014",
				"a(k) = det(S(2,k,1)). - _Ryan Stees_, Dec 15 2014",
				"a(n) = 1/(1/(n+1)+1/(n+1)^2+1/(n+1)^3+.... - _Pierre CAMI_, Jan 22 2015",
				"a(n) = Sum_{m=0..n-1} Stirling1(n-1,m)*Bell(m+1), for n \u003e= 1. This corresponds to Bell(m+1) = Sum_{k=0..m} Stirling2(m, k)*(k+1), for m \u003e= 0, from the fact that Stirling2*Stirling1 = identity matrix. See A048993, A048994 and A000110. - _Wolfdieter Lang_, Feb 03 2015",
				"a(n) = Sum_{k=1...2n-1}(-1)^(k+1)*k*(2n-k). In addition, surprisingly, a(n) = Sum_{k=1...2n-1}(-1)^(k+1)*k^2*(2n-k)^2. - _Charlie Marion_, Jan 05 2016",
				"G.f.: x/(1-x)^2 = (x * r(x) *r(x^3) * r(x^9) * r(x^27) *...), where r(x) = (1 + x + x^2)^2 = (1 + 2x + 3x^2 + 2x^3 + x^4). - _Gary W. Adamson_, Jan 11 2017"
			],
			"maple": [
				"A000027 := n-\u003en; seq(A000027(n), n=1..100);"
			],
			"mathematica": [
				"Range@ 77 (* _Robert G. Wilson v_, Mar 31 2015 *)"
			],
			"program": [
				"(MAGMA) [ n : n in [1..100]];",
				"(PARI) {a(n) = n};",
				"(R) 1:100",
				"(Shell) seq 1 100",
				"(Haskell)",
				"a000027 = id",
				"a000027_list = [1..]  -- _Reinhard Zumkeller_, May 07 2012",
				"(Maxima) makelist(n, n, 1, 30); /* _Martin Ettl_, Nov 07 2012 */"
			],
			"xref": [
				"A001477 = nonnegative numbers.",
				"Partial sums of A000012.",
				"Cf. A001478, A001906, A007931, A007932, A027641, A074909, A178568, A194807.",
				"Cf. A026081 = integers in reverse alphabetical order in U.S. English, A107322 = English name for number and its reverse have the same number of letters, A119796 = zero through ten in alphabetical order of English reverse spelling, A005589, etc. Cf. A185787 (includes a list of sequences based on the natural number array A000027).",
				"Cf. Boustrophedon transforms: A000737, A231179;",
				"Cf. A038722 (mirrored when seen as triangle), A056011 (boustrophedon).",
				"Cf. A048993, A048994, A000110 (see the Feb 03 2015 formula).",
				"Cf. A289187,"
			],
			"keyword": "core,nonn,easy,mult,tabl",
			"offset": "1,2",
			"author": "_N. J. A. Sloane_",
			"ext": [
				"Links edited by _Daniel Forgues_, Oct 07 2009"
			],
			"references": 1726,
			"revision": 529,
			"time": "2019-10-26T07:08:33-04:00",
			"created": "1991-04-30T03:00:00-04:00"
		},
		{
			"number": 7953,
			"data": "0,1,2,3,4,5,6,7,8,9,1,2,3,4,5,6,7,8,9,10,2,3,4,5,6,7,8,9,10,11,3,4,5,6,7,8,9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,9,10,11,12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15",
			"name": "Digital sum (i.e., sum of digits) of n; also called digsum(n).",
			"comment": [
				"Do not confuse with the digital root of n, A010888 (first term that differs is a(19)).",
				"Also the fixed point of the morphism 0 -\u003e {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 1 -\u003e {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, 2 -\u003e {2, 3, 4, 5, 6, 7, 8, 9, 10, 11}, etc. - _Robert G. Wilson v_, Jul 27 2006",
				"For n \u003c 100 equal to (floor(n/10) + n mod 10) = A076314(n). - _Hieronymus Fischer_, Jun 17 2007",
				"a(n) = A138530(n, 10) for n \u003e 9. - _Reinhard Zumkeller_, Mar 26 2008",
				"a(A058369(n)) = A004159(A058369(n)); a(A000290(n)) = A004159(n). - _Reinhard Zumkeller_, Apr 25 2009",
				"a(n) mod 2 = A179081(n). - _Reinhard Zumkeller_, Jun 28 2010"
			],
			"reference": [
				"Krassimir Atanassov, On the 16th Smarandache Problem, Notes on Number Theory and Discrete Mathematics, Sophia, Bulgaria, Vol. 5 (1999), No. 1, 36-38."
			],
			"link": [
				"N. J. A. Sloane, \u003ca href=\"/A007953/b007953.txt\"\u003eTable of n, a(n) for n = 0..10000\u003c/a\u003e",
				"Krassimir Atanassov, \u003ca href=\"http://www.gallup.unm.edu/~smarandache/Atanassov-SomeProblems.pdf\"\u003eOn Some of Smarandache's Problems\u003c/a\u003e",
				"Jean-Luc Baril, \u003ca href=\"http://www.combinatorics.org/ojs/index.php/eljc/article/view/v18i1p178\"\u003eClassical sequences revisited with permutations avoiding dotted pattern\u003c/a\u003e, Electronic Journal of Combinatorics, 18 (2011), #P178.",
				"Ernesto Estrada, Puri Pereira-Ramos, \u003ca href=\"https://doi.org/10.1155/2018/9893867\"\u003eSpatial 'Artistic' Networks: From Deconstructing Integer-Functions to Visual Arts\u003c/a\u003e, Complexity, Vol. 2018 (2018), Article ID 9893867.",
				"A. O. Gel'fond, \u003ca href=\"http://matwbn.icm.edu.pl/ksiazki/aa/aa13/aa13115.pdf\"\u003eSur les nombres qui ont des propriétés additives et multiplicatives données\u003c/a\u003e (French) Acta Arith. 13 1967/1968 259--265. MR0220693 (36 #3745)",
				"Christian Mauduit \u0026 András Sárközy, \u003ca href=\"http://dx.doi.org/10.1006/jnth.1998.2229\"\u003eOn the arithmetic structure of sets characterized by sum of digits properties\u003c/a\u003e J. Number Theory 61(1996), no. 1, 25--38. MR1418316 (97g:11107)",
				"Christian Mauduit \u0026 András Sárközy, \u003ca href=\"http://matwbn.icm.edu.pl/ksiazki/aa/aa81/aa8122.pdf\"\u003e On the arithmetic structure of the integers whose sum of digits is fixed\u003c/a\u003e, Acta Arith. 81 (1997), no. 2, 145--173. MR1456239 (99a:11096)",
				"Kerry Mitchell, \u003ca href=\"http://kerrymitchellart.com/articles/Spirolateral-Type_Images_from_Integer_Sequences.pdf\"\u003eSpirolateral-Type Images from Integer Sequences\u003c/a\u003e, 2013",
				"Kerry Mitchell, \u003ca href=\"/A007953/a007953.jpg\"\u003eSpirolateral image for this sequence\u003c/a\u003e [taken, with permission, from the Spirolateral-Type Images from Integer Sequences article]",
				"Jan-Christoph Puchta, Jürgen Spilker, \u003ca href=\"http://dx.doi.org/10.1007/s00591-002-0048-4\"\u003eAltes und Neues zur Quersumme\u003c/a\u003e, Math. Semesterber, 49 (2002), 209-226.",
				"J.-C. Puchta, J. Spilker, \u003ca href=\"http://www.math.uni-rostock.de/~schlage-puchta/papers/Quersumme.pdf\"\u003eAltes und Neues zur Quersumme\u003c/a\u003e",
				"Maxwell Schneider, Robert Schneider, \u003ca href=\"https://arxiv.org/abs/1807.06710\"\u003eDigit sums and generating functions\u003c/a\u003e, arXiv:1807.06710 [math.NT], 2018.",
				"Vladimir Shevelev, \u003ca href=\"http://journals.impan.pl/aa/Inf/126-3-1.html\"\u003eCompact integers and factorials\u003c/a\u003e, Acta Arith. 126 (2007), no.3,195-236 (cf. pp.205-206).",
				"Robert Walker, \u003ca href=\"http://robertinventor.com/ftswiki/Self_Similar_Sloth_Canon_Number_Sequences\"\u003eSelf Similar Sloth Canon Number Sequences\u003c/a\u003e",
				"Eric Weisstein's World of Mathematics, \u003ca href=\"http://mathworld.wolfram.com/DigitSum.html\"\u003eDigit Sum\u003c/a\u003e",
				"Wikipedia, \u003ca href=\"http://en.wikipedia.org/wiki/Digit_sum\"\u003eDigit sum\u003c/a\u003e",
				"\u003ca href=\"/index/Coi#Colombian\"\u003eIndex entries for Colombian or self numbers and related sequences\u003c/a\u003e"
			],
			"formula": [
				"a(n) \u003c= 9(log_10(n)+1). - _Stefan Steinerberger_, Mar 24 2006",
				"a(0) = 0, a(10n+i) = a(n) + i 0 \u003c= i \u003c= 9; a(n) = n - 9*(sum(k \u003e 0,  floor(n/10^k)) = n - 9*A054899(n). - _Benoit Cloitre_, Dec 19 2002",
				"From _Hieronymus Fischer_, Jun 17 2007: (Start)",
				"G.f. g(x) = sum{k \u003e 0, (x^k - x^(k+10^k) - 9x^(10^k))/(1-x^(10^k))}/(1-x).",
				"a(n) = n - 9*sum{10 \u003c= k \u003c= n, sum{j|k, j \u003e= 10, floor(log_10(j)) - floor(log_10(j-1))}}. (End)",
				"From _Hieronymus Fischer_, Jun 25 2007: (Start)",
				"The g.f. can be expressed in terms of a Lambert series, in that g(x) = (x/(1-x) - 9*L[b(k)](x))/(1-x) where L[b(k)](x) = sum{k \u003e= 0, b(k)*x^k/(1-x^k)} is a Lambert series with b(k) = 1, if k \u003e 1 is a power of 10, else b(k) = 0.",
				"G.f.: g(x) = sum{k \u003e 0, (1 - 9*c(k))*x^k}/(1-x), where c(k) = sum{j \u003e 1, j|k,  floor(log_10(j)) - floor(log_10(j-1))}.",
				"a(n) = n - 9*sum_{0 \u003c k \u003c= floor(log_10(n))} a(floor(n/10^k))*10^(k-1). (End)",
				"From _Hieronymus Fischer_, Oct 06 2007: (Start)",
				"a(n) \u003c= 9*(1 + floor(log_10(n)), equality holds for n = 10^m - 1, m \u003e 0.",
				"lim sup (a(n) - 9*log_10(n)) = 0 for n --\u003e infinity.",
				"lim inf (a(n+1) - a(n) + 9*log_10(n)) = 1 for n --\u003e infinity. (End)",
				"a(A051885(n)) = n.",
				"a(n) \u003c= 9*log_10(n+1). - _Vladimir Shevelev_, Jun 01 2011",
				"a(n) = a(n-1) + a(n-10) - a(n-11), for n \u003c 100. - _Alexander R. Povolotsky_, Oct 09 2011",
				"a(n) = Sum_k \u003e= 0 {A031298(n, k)}. - _Philippe Deléham_, Oct 21 2011",
				"a(n) = a(n mod b^k) + a(floor(n/b^k)), for all k \u003e= 0. - _Hieronymus Fischer_, Mar 24 2014"
			],
			"example": [
				"a(123) = 1 + 2 + 3 = 6, a(9875) = 9 + 8 + 7 + 5 = 29."
			],
			"maple": [
				"A007953 := proc(n) add(d,d=convert(n,base,10)) ; end proc: # _R. J. Mathar_, Mar 17 2011"
			],
			"mathematica": [
				"Table[Sum[DigitCount[n][[i]] * i, {i, 9}], {n, 50}] (* _Stefan Steinerberger_, Mar 24 2006 *)",
				"Table[Plus @@ IntegerDigits @ n, {n, 0, 87}] (* or *)",
				"Nest[Flatten[# /. a_Integer -\u003e Array[a + # \u0026, 10, 0]] \u0026, {0}, 2] (* _Robert G. Wilson v_, Jul 27 2006 *)",
				"Table[Sum[Floor[n/10^k] - 10 * Floor[n/10^(k + 1)], {k, 0, Floor[Log[10, n]]}], {n, 300}] (* _José de Jesús Camacho Medina_, Mar 31 2014 *)",
				"Total/@IntegerDigits[Range[0,90]] (* _Harvey P. Dale_, May 10 2016 *)"
			],
			"program": [
				"/* The next few PARI programs are kept for historical and pedagogical reasons.",
				"   For practical use, the suggested and most efficient code is: A007953=sumdigits */",
				"(PARI) a(n)=if(n\u003c1, 0, if(n%10, a(n-1)+1, a(n/10))) \\\\ Recursive, very inefficient. A more efficient recursive variant: a(n)=if(n\u003e9, n=divrem(n, 10); n[2]+a(n[1]), n)",
				"(PARI) a(n, b=10)={my(s=(n=divrem(n, b))[2]); while(n[1]\u003e=b, s+=(n=divrem(n[1], b))[2]); s+n[1]} \\\\ _M. F. Hasler_, Mar 22 2011",
				"(PARI) a(n)=sum(i=1, #n=digits(n), n[i]) \\\\ Twice as fast. Not so nice but faster:",
				"(PARI) a(n)=sum(i=1,#n=Vecsmall(Str(n)),n[i])-48*#n \\\\ - _M. F. Hasler_, May 10 2015",
				"/* Since PARI 2.7, one can also use: a(n)=vecsum(digits(n)), or better: A007953=sumdigits. [Edited and commented by _M. F. Hasler_, Nov 09 2018] */",
				"(PARI) a(n) = sumdigits(n); \\\\ _Altug Alkan_, Apr 19 2018",
				"(Haskell)",
				"a007953 n | n \u003c 10 = n",
				"          | otherwise = a007953 n' + r where (n',r) = divMod n 10",
				"-- _Reinhard Zumkeller_, Nov 04 2011, Mar 19 2011",
				"(MAGMA) [ \u0026+Intseq(n): n in [0..87] ];  // _Bruno Berselli_, May 26 2011",
				"(Smalltalk)",
				"\"Recursive version for general bases. Set base = 10 for this sequence.\"",
				"digitalSum: base",
				"| s |",
				"base = 1 ifTrue: [^self].",
				"(s := self // base) \u003e 0",
				"  ifTrue: [^(s digitalSum: base) + self - (s * base)]",
				"  ifFalse: [^self]",
				"\"by _Hieronymus Fischer_, Mar 24 2014\"",
				"(Python)",
				"def A007953(n):",
				"    return sum(int(d) for d in str(n)) # _Chai Wah Wu_, Sep 03 2014",
				"(Scala) (0 to 99).map(_.toString.map(_.toInt - 48).sum) // _Alonso del Arte_, Sep 15 2019"
			],
			"xref": [
				"Cf. A003132, A055012, A055013, A055014, A055015, A010888, A007954, A031347, A055017, A076313, A076314, A007953, A054899, A138470, A138471, A138472, A000120, A004426, A004427, A054683, A054684, A069877, A179082-A179085, A108971, A179987, A179988, A180018, A180019, A217928, A216407, A037123, A074784, A231688, A231689, A225693, A254524 (ordinal transform).",
				"For n + digsum(n) see A062028."
			],
			"keyword": "nonn,base,nice,easy,look",
			"offset": "0,3",
			"author": "R. Muller",
			"ext": [
				"More terms from _Hieronymus Fischer_, Jun 17 2007",
				"Edited by _Michel Marcus_, Nov 11 2013"
			],
			"references": 873,
			"revision": 224,
			"time": "2019-09-16T02:08:30-04:00",
			"created": "1996-03-15T03:00:00-05:00"
		},
		{
			"number": 961,
			"id": "M0517 N0185",
			"data": "1,2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,53,59,61,64,67,71,73,79,81,83,89,97,101,103,107,109,113,121,125,127,128,131,137,139,149,151,157,163,167,169,173,179,181,191,193,197,199,211,223,227",
			"name": "Powers of primes. Alternatively, 1 and the prime powers (p^k, p prime, k \u003e= 1).",
			"comment": [
				"Of course 1 = p^0 for any prime p, so 1 is definitely the power of a prime.",
				"The term \"prime power\" is ambiguous. To a mathematician it means any number p^k, p prime, k \u003e= 0, including 1.",
				"Any nonzero integer is a product of primes and units, where the units are +1 and -1. This is tied to the Fundamental Theorem of Arithmetic which proves that the factorizations are unique up to order and units. (So, since 1 = p^0 does not have a well defined prime base p, it is sometimes not regarded as a prime power. See A246655 for the sequence without 1.)",
				"These numbers are (apart from 1) the numbers of elements in finite fields. - _Franz Vrabec_, Aug 11 2004",
				"Numbers whose divisors form a geometrical progression. The divisors of p^k are 1, p, p^2, p^3, ...p^k. - _Amarnath Murthy_, Jan 09 2002",
				"a(n) = A025473(n)^A025474(n). - _David Wasserman_, Feb 16 2006",
				"a(n) = A117331(A117333(n)). - _Reinhard Zumkeller_, Mar 08 2006",
				"These are also precisely the orders of those finite affine planes that are known to exist as of today. (The order of a finite affine plane is the number of points in an arbitrarily chosen line of that plane. This number is unique for all lines comprise the same number of points.) - Peter C. Heinig (algorithms(AT)gmx.de), Aug 09 2006",
				"Except for first term, the index of the second number divisible by n in A002378, if the index equals n. - _Mats Granvik_, Nov 18 2007",
				"These are precisely the numbers such that lcm(1,...,m-1)\u003clcm(1,...,m) (=A003418(m) for m\u003e0; here for m=1, the l.h.s. is taken to be 0). We have a(n+1)=a(n)+1 if a(n) is a Mersenne prime or a(n)+1 is a Fermat prime; the converse is true except for n=7 (from Catalan's conjecture) and n=1, since 2^1-1 and 2^0+1 are not considered as Mersenne resp. Fermat prime. - _M. F. Hasler_, Jan 18 2007, Apr 18 2010",
				"The sequence is A000015 without repetitions, or more formally, A000961=Union[A000015]. - _Zak Seidov_, Feb 06 2008",
				"Except for a(1)=1, indices for which the cyclotomic polynomial Phi[k] yields a prime at x=1, cf. A020500. - _M. F. Hasler_, Apr 04 2008",
				"Also, {A138929(k) ; k\u003e1} = {2*A000961(k) ; k\u003e1} = {4,6,8,10,14,16,18,22,26,32,34,38,46,50,54,58,62,64,74,82,86,94,98,...} are exactly the indices for which Phi[k](-1) is prime. - _M. F. Hasler_, Apr 04 2008",
				"A143201(a(n)) = 1. - _Reinhard Zumkeller_, Aug 12 2008",
				"Number of distinct primes dividing n=omega(n)\u003c2. - _Juri-Stepan Gerasimov_, Oct 30 2009",
				"Numbers n such that sum{p-1|p is prime and divisor of n}=product{p-1|p is prime and divisor of n}. A055631(n)=A173557(n-1). - _Juri-Stepan Gerasimov_, Dec 09 2009, Mar 10 2010",
				"Numbers n such that A028236(n) = 1. _Klaus Brockhaus_, Nov 06 2010",
				"A188666(k) = a(k+1) for k: 2*a(k) \u003c= k \u003c 2*a(k+1), k \u003e 0; notably a(n+1) = A188666(2*a(n)). - _Reinhard Zumkeller_, Apr 25 2011",
				"A003415(a(n)) = A192015(n); A068346(a(n)) = A192016(n); a(n)=A192134(n)+A192015(n). - _Reinhard Zumkeller_, Jun 26 2011",
				"A089233(a(n)) = 0. - _Reinhard Zumkeller_, Sep 04 2013",
				"The positive integers n such that every element of the symmetric group S_n which has order n is an n-cycle. - _W. Edwin Clark_, Aug 05 2014",
				"Conjecture: these are numbers m such that Sum_{k=0..m-1} k^phi(m) == phi(m) (mod m), where phi(m) = A000010(m). - _Thomas Ordowski_ and _Giovanni Resta_, Jul 25 2018",
				"Numbers whose (increasingly ordered) divisors are alternatingly squares and nonsquares. - _Michel Marcus_, Jan 16 2019"
			],
			"reference": [
				"M. Abramowitz and I. A. Stegun, eds., Handbook of Mathematical Functions, National Bureau of Standards Applied Math. Series 55, 1964 (and various reprintings), p. 870.",
				"M. Koecher and A. Krieg, Ebene Geometrie, Springer, 1993",
				"R. Lidl and H. Niederreiter, Introduction to Finite Fields and Their Applications, Cambridge 1986, Theorem 2.5, p. 45.",
				"N. J. A. Sloane, A Handbook of Integer Sequences, Academic Press, 1973 (includes this sequence).",
				"N. J. A. Sloane and Simon Plouffe, The Encyclopedia of Integer Sequences, Academic Press, 1995 (includes this sequence)."
			],
			"link": [
				"T. D. Noe, \u003ca href=\"/A000961/b000961.txt\"\u003eTable of n, a(n) for n = 1..10000\u003c/a\u003e",
				"M. Abramowitz and I. A. Stegun, eds., \u003ca href=\"http://www.convertit.com/Go/ConvertIt/Reference/AMS55.ASP\"\u003eHandbook of Mathematical Functions\u003c/a\u003e, National Bureau of Standards, Applied Math. Series 55, Tenth Printing, 1972 [alternative scanned copy].",
				"Brady Haran and Günter Ziegler, \u003ca href=\"https://www.youtube.com/watch?v=5SfXqTENV_Q\"\u003eCannons and Sparrows\u003c/a\u003e, Numberphile video (2018)",
				"Laurentiu Panaitopol, \u003ca href=\"http://dx.doi.org/10.1216/rmjm/1021249445\"\u003eSome of the properties of the sequence of powers of prime numbers\u003c/a\u003e, Rocky Mountain Journal of Mathematics, Volume 31, Number 4, Winter 2001.",
				"Eric Weisstein's World of Mathematics, \u003ca href=\"http://mathworld.wolfram.com/PrimePower.html\"\u003ePrime Power\u003c/a\u003e",
				"Eric Weisstein's World of Mathematics, \u003ca href=\"http://mathworld.wolfram.com/ProjectivePlane.html\"\u003eProjective Plane\u003c/a\u003e",
				"\u003ca href=\"/index/Cor#core\"\u003eIndex entries for \"core\" sequences\u003c/a\u003e"
			],
			"formula": [
				"Panaitopol (2001) gives many properties, inequalities and asymptotics. - _N. J. A. Sloane_, Oct 31 2014",
				"m=a(n) for some n \u003c=\u003e lcm(1,...,m-1)\u003clcm(1,...,m), where lcm(1...0):=0 as to include a(1)=1. a(n+1)=a(n)+1 \u003c=\u003e a(n+1)=A019434(k) or a(n)=A000668(k) for some k (by Catalan's conjecture), except for n=1 and n=7. - _M. F. Hasler_, Jan 18 2007, Apr 18 2010",
				"A001221(a(n)) \u003c 2. - _Juri-Stepan Gerasimov_, Oct 30 2009",
				"A008480(a(n)) = 1 for all n \u003e= 1. - _Alois P. Heinz_, May 26 2018"
			],
			"maple": [
				"readlib(ifactors): for n from 1 to 250 do if nops(ifactors(n)[2])=1 then printf(`%d,`,n) fi: od:",
				"A000961 := proc(n)",
				"    option remember;",
				"    local k ;",
				"    if n = 1 then",
				"        1;",
				"    else",
				"        for k from procname(n-1)+1 do",
				"            if nops(numtheory[factorset](k)) = 1 then",
				"                return k ;",
				"            end if;",
				"        end do:",
				"    end if;",
				"end proc: # _Alois P. Heinz_, Apr 08 2013"
			],
			"mathematica": [
				"Select[ Range[ 2, 250 ], Mod[ #, # - EulerPhi[ # ] ] == 0 \u0026 ]",
				"Select[ Range[ 2, 250 ], Length[FactorInteger[ # ] ] == 1 \u0026 ]",
				"max = 0; a = {}; Do[m = FactorInteger[n]; w = Sum[m[[k]][[1]]^m[[k]][[2]], {k, 1, Length[m]}]; If[w \u003e max, AppendTo[a, n]; max = w], {n, 1, 1000}]; a (* _Artur Jasinski_ *)",
				"Join[{1}, Select[Range[2, 250], PrimePowerQ]] (* _Jean-François Alcover_, Jul 07 2015 *)"
			],
			"program": [
				"(MAGMA) [1] cat [ n : n in [2..250] | IsPrimePower(n) ]; // corrected by Arkadiusz Wesolowski, Jul 20 2012",
				"(PARI) A000961(n,l=-1,k=0)=until(n--\u003c1,until(l\u003clcm(l,k++),); l=lcm(l,k));k",
				"print_A000961(lim=999,l=-1)=for(k=1,lim, l==lcm(l,k) \u0026\u0026 next; l=lcm(l,k); print1(k,\",\")) \\\\ _M. F. Hasler_, Jan 18 2007",
				"(PARI) isA000961(n) = (omega(n) == 1 || n == 1) \\\\ _Michael B. Porter_, Sep 23 2009",
				"(PARI) nextA000961(n)=my(m,r,p);m=2*n;for(e=1,ceil(log(n+0.01)/log(2)),r=(n+0.01)^(1/e);p=prime(primepi(r)+1);m=min(m,p^e));m \\\\ _Michael B. Porter_, Nov 02 2009",
				"(PARI) is(n)=isprimepower(n) || n==1 \\\\ _Charles R Greathouse IV_, Nov 20 2012",
				"(PARI) list(lim)=my(v=primes(primepi(lim)),u=List([1])); forprime(p=2,sqrtint(lim\\1),for(e=2,log(lim+.5)\\log(p),listput(u,p^e))); vecsort(concat(v,Vec(u))) \\\\ _Charles R Greathouse IV_, Nov 20 2012",
				"(Haskell)",
				"import Data.Set (singleton, deleteFindMin, insert)",
				"a000961 n = a000961_list !! (n-1)",
				"a000961_list = 1 : g (singleton 2) (tail a000040_list) where",
				"g s (p:ps) = m : g (insert (m * a020639 m) $ insert p s') ps",
				"where (m, s') = deleteFindMin s",
				"-- _Reinhard Zumkeller_, May 01 2012, Apr 25 2011",
				"(Sage)",
				"def A000961_list(n) :",
				"R = [1]",
				"for i in (2..n) :",
				"if i.is_prime_power() : R.append(i)",
				"return R",
				"A000961_list(227) # _Peter Luschny_, Feb 07 2012",
				"(Python)",
				"from sympy import primerange",
				"A000961_list = [1]",
				"for p in primerange(1,m):",
				"....pe = p",
				"....while pe \u003c m:",
				"........A000961_list.append(pe)",
				"........pe *= p",
				"A000961_list = sorted(A000961_list) # _Chai Wah Wu_, Sep 08 2014"
			],
			"xref": [
				"There are four different sequences which may legitimately be called \"prime powers\": A000961 (p^k, k \u003e= 0), A246655 (p^k, k \u003e= 1), A246547 (p^k, k \u003e= 2), A025475 (p^k, k=0 and k \u003e= 2). When you refer to \"prime powers\", be sure to specify which of these you mean. Also A001597 is the sequence of nontrivial powers n^k, n \u003e= 1, k \u003e= 2. - _N. J. A. Sloane_, Mar 24 2018",
				"Cf. A008480, A010055, A065515, A095874, A025473.",
				"Cf. indices of record values of A003418; A000668 and A019434 give a member of twin pairs a(n+1)=a(n)+1.",
				"A138929(n) = 2*a(n).",
				"Cf. A000040, A001221, A001477. - _Juri-Stepan Gerasimov_, Dec 09 2009",
				"A028236 (if n = Product (p_j^k_j), a(n) = numerator of Sum 1/p_j^k_j). - _Klaus Brockhaus_, Nov 06 2010",
				"A000015(n) = Min{term : \u003e= n}; A031218(n) = Max{term : \u003c= n}.",
				"Complementary (in the positive integers) to sequence A024619. - _Jason Kimberley_, Nov 10 2015"
			],
			"keyword": "nonn,easy,core,nice",
			"offset": "1,2",
			"author": "_N. J. A. Sloane_",
			"ext": [
				"Corrected comment and formula referring to Catalan's conjecture _M. F. Hasler_, Apr 18 2010",
				"Description modified by _Ralf Stephan_, Aug 29 2014"
			],
			"references": 693,
			"revision": 168,
			"time": "2019-04-24T16:06:35-04:00",
			"created": "1991-04-30T03:00:00-04:00"
		},
		{
			"number": 1477,
			"data": "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77",
			"name": "The nonnegative integers.",
			"comment": [
				"Although this is a list, and lists normally have offset 1, it seems better to make an exception in this case. - _N. J. A. Sloane_, Mar 13 2010",
				"The subsequence 0,1,2,3,4 gives the known values of n such that 2^(2^n)+1 is a prime (see A019434, the Fermat primes). - _N. J. A. Sloane_, Jun 16 2010",
				"a(n) = A007966(n)*A007967(n). - _Reinhard Zumkeller_, Jun 18 2011",
				"Also: The identity map, defined on the set of nonnegative integers. The restriction to the positive integers yields the sequence A000027. - _M. F. Hasler_, Nov 20 2013",
				"The number of partitions of 2n into exactly 2 parts. - _Colin Barker_, Mar 22 2015",
				"The number of orbits of Aut(Z^7) as function of the infinity norm n of the representative lattice point of the orbit, when the cardinality of the orbit is equal to 8960 or 168.- _Philippe A.J.G. Chevalier_, Dec 29 2015",
				"Partial sums give A000217. - _Omar E. Pol_, Jul 26 2018"
			],
			"link": [
				"N. J. A. Sloane, \u003ca href=\"/A001477/b001477.txt\"\u003eTable of n, a(n) for n = 0..500000\u003c/a\u003e",
				"Paul Barry, \u003ca href=\"https://cs.uwaterloo.ca/journals/JIS/VOL8/Barry/barry84.html\"\u003eA Catalan Transform and Related Transformations on Integer Sequences\u003c/a\u003e, Journal of Integer Sequences, Vol. 8 (2005), Article 05.4.5.",
				"Hans Havermann, \u003ca href=\"/A001477/a001477.txt\"\u003eTable giving n and American English name for n, for 0 \u003c= n \u003c= 100999, without spaces or hyphens\u003c/a\u003e",
				"Hans Havermann, \u003ca href=\"http://chesswanks.com/num/NumberNames.txt\"\u003eAmerican English number names to one million, without spaces or hyphens\u003c/a\u003e",
				"Tanya Khovanova, \u003ca href=\"http://www.tanyakhovanova.com/RecursiveSequences/RecursiveSequences.html\"\u003eRecursive Sequences\u003c/a\u003e",
				"Luis Manuel Rivera, \u003ca href=\"http://arxiv.org/abs/1406.3081\"\u003eInteger sequences and k-commuting permutations\u003c/a\u003e, arXiv preprint arXiv:1406.3081 [math.CO], 2014-2015.",
				"László Németh, \u003ca href=\"https://cs.uwaterloo.ca/journals/JIS/VOL21/Nemeth/nemeth6.html\"\u003eThe trinomial transform triangle\u003c/a\u003e, J. Int. Seqs., Vol. 21 (2018), Article 18.7.3. Also \u003ca href=\"https://arxiv.org/abs/1807.07109\"\u003earXiv:1807.07109\u003c/a\u003e [math.NT], 2018.",
				"Eric Weisstein's World of Mathematics, \u003ca href=\"http://mathworld.wolfram.com/NaturalNumber.html\"\u003eNatural Number\u003c/a\u003e",
				"Eric Weisstein's World of Mathematics, \u003ca href=\"http://mathworld.wolfram.com/NonnegativeInteger.html\"\u003eNonnegative Integer\u003c/a\u003e",
				"\u003ca href=\"/index/Cor#core\"\u003eIndex entries for \"core\" sequences\u003c/a\u003e",
				"\u003ca href=\"/index/Per#IntegerPermutation\"\u003eIndex entries for sequences that are permutations of the natural numbers\u003c/a\u003e",
				"\u003ca href=\"/index/Rec#order_02\"\u003eIndex entries for linear recurrences with constant coefficients\u003c/a\u003e, signature (2,-1)."
			],
			"formula": [
				"a(n) = n.",
				"a(0) = 0, a(n) = a(n-1) + 1.",
				"G.f.: x/(1-x)^2.",
				"Multiplicative with a(p^e) = p^e. - _David W. Wilson_, Aug 01 2001",
				"When seen as array: T(k, n) = n + (k+n)*(k+n+1)/2. Main diagonal is 2n(n+1) (A046092), antidiagonal sums are n(n+1)(n+2)/2 (A027480). - _Ralf Stephan_, Oct 17 2004",
				"Dirichlet generating function: zeta(s-1). - _Franklin T. Adams-Watters_, Sep 11 2005.",
				"E.g.f.: x*e^x. - _Franklin T. Adams-Watters_, Sep 11 2005",
				"a(0)=0, a(1)=1, a(n) = 2*a(n-1) - a(n-2). - _Jaume Oliver Lafont_, May 07 2008",
				"Alternating partial sums give A001057 = A000217 - 2*(A008794). - _Eric Desbiaux_, Oct 28 2008",
				"a(n) = 2*A080425(n) + 3*A008611(n-3), n\u003e1. - _Eric Desbiaux_, Nov 15 2009",
				"a(n) = Sum_{k\u003e=0} A030308(n,k)*2^k. - _Philippe Deléham_, Oct 20 2011",
				"a(n) = 2*A028242(n-1) + (-1)^n*A000034(n-1). - _R. J. Mathar_, Jul 20 2012",
				"a(n+1) = det(C(i+1,j), 1 \u003c= i,j \u003c= n), where C(n,k) are binomial coefficients. - _Mircea Merca_, Apr 06 2013",
				"a(n-1) = floor(n/e^(1/n)) for n \u003e 0. - _Richard R. Forberg_, Jun 22 2013",
				"a(n) = A000027(n) for all n\u003e0.",
				"a(n) = floor(cot(1/(n+1))). - _Clark Kimberling_, Oct 08 2014",
				"a(0)=0, a(n\u003e0) = 2z(-1)^[( |z|/z + 3 )/2] + ( |z|/z - 1 )/2 for z=A130472(n\u003e0); a 1_to_1 correspondence between integers and naturals. - _Adriano Caroli_, Mar 29 2015"
			],
			"example": [
				"Triangular view:",
				"   0",
				"   1   2",
				"   3   4   5",
				"   6   7   8   9",
				"  10  11  12  13  14",
				"  15  16  17  18  19  20",
				"  21  22  23  24  25  26  27",
				"  28  29  30  31  32  33  34  35",
				"  36  37  38  39  40  41  42  43  44",
				"  45  46  47  48  49  50  51  52  53  54"
			],
			"maple": [
				"[ seq(n,n=0..100) ];"
			],
			"mathematica": [
				"Table[n, {n, 0, 100}] (* _Stefan Steinerberger_, Apr 08 2006 *)",
				"LinearRecurrence[{2, -1}, {0, 1}, 77] (* _Robert G. Wilson v_, May 23 2013 *)",
				"CoefficientList[ Series[x/(x - 1)^2, {x, 0, 76}], x] (* _Robert G. Wilson v_, May 23 2013 *)"
			],
			"program": [
				"(MAGMA) [ n : n in [0..100]];",
				"(PARI) A001477(n)=n /* first term is a(0) */",
				"(Haskell)",
				"a001477 = id",
				"a001477_list = [0..]  -- _Reinhard Zumkeller_, May 07 2012"
			],
			"xref": [
				"Cf. A000027 (n\u003e=1).",
				"Partial sums of A057427. - _Jeremy Gardiner_, Sep 08 2002",
				"Cf. A038608 (alternating signs), A001787 (binomial transform).",
				"Cf. A055112.",
				"Cf. Boustrophedon transforms: A231179, A000737.",
				"Cf. A245422.",
				"Number of orbits of Aut(Z^7) as function of the infinity norm A000579, A154286, A102860, A002412, A045943, A115067, A008586, A008585, A005843, A000217.",
				"When written as an array, the rows/columns are A000217, A000124, A152948, A152950, A145018, A167499, A166136, A167487... and A000096, A034856, A055998, A046691, A052905, A055999... (with appropriate offsets); cf. analogous lists for A000027 in A185787."
			],
			"keyword": "core,nonn,easy,mult,tabl",
			"offset": "0,3",
			"author": "_N. J. A. Sloane_",
			"references": 679,
			"revision": 251,
			"time": "2019-11-21T04:40:13-05:00",
			"created": "1991-04-30T03:00:00-04:00"
		},
		{
			"number": 2113,
			"id": "M0484 N0178",
			"data": "0,1,2,3,4,5,6,7,8,9,11,22,33,44,55,66,77,88,99,101,111,121,131,141,151,161,171,181,191,202,212,222,232,242,252,262,272,282,292,303,313,323,333,343,353,363,373,383,393,404,414,424,434,444,454,464,474,484,494,505,515",
			"name": "Palindromes in base 10.",
			"comment": [
				"n is a palindrome (i.e., a(k) = n for some k) if and only if n = A004086(n). - _Reinhard Zumkeller_, Mar 10 2002",
				"A178788(a(n)) = 0 for n \u003e 9. - _Reinhard Zumkeller_, Jun 30 2010",
				"A064834(a(n)) = 0. - _Reinhard Zumkeller_, Sep 18 2013",
				"It seems that if n*reversal(n) is in the sequence then n = 3 or all digits of n are less than 3. - _Farideh Firoozbakht_, Nov 02 2014",
				"The position of a palindrome within the sequence can be determined almost without calculation: If the palindrome has an even number of digits, prepend a 1 to the front half of the palindrome's digits. If the number of digits is odd, prepend the value of front digit + 1 to the digits from position 2 ... central digit. Examples: 98766789 = a(19876), 515 = a(61), 8206028 = a(9206), 9230329 = a(10230). - _Hugo Pfoertner_, Aug 14 2015",
				"This sequence is an additive basis of order at most 49, see Banks link. - _Charles R Greathouse IV_, Aug 23 2015",
				"The order has been reduced from 49 to 3; see the Cilleruelo-Luca and Cilleruelo-Luca-Baxter links. - _Jonathan Sondow_, Nov 27 2017",
				"See A262038 for the \"next palindrome\" and A261423 for the \"preceding palindrome\" functions. - _M. F. Hasler_, Sep 09 2015",
				"The number of palindromes with d digits is 10 if d = 1, and otherwise it is 9 * 10^(floor((d - 1)/2)). - _N. J. A. Sloane_, Dec 06 2015",
				"Sequence A033665 tells how many iterations of the Reverse-then-add function A056964 are needed to reach a palindrome; numbers for which this will never happen are Lychrel numbers (A088753) or rather Kin numbers (A023108). - _M. F. Hasler_, Apr 13 2019"
			],
			"reference": [
				"Karl G. Kröber, \"Palindrome, Perioden und Chaoten: 66 Streifzüge durch die palindromischen Gefilde\" (1997, Deutsch-Taschenbücher; Bd. 99) ISBN 3-8171-1522-9.",
				"Clifford A. Pickover, A Passion for Mathematics, Wiley, 2005; see p. 71.",
				"N. J. A. Sloane, A Handbook of Integer Sequences, Academic Press, 1973 (includes this sequence).",
				"N. J. A. Sloane and Simon Plouffe, The Encyclopedia of Integer Sequences, Academic Press, 1995 (includes this sequence)."
			],
			"link": [
				"T. D. Noe, \u003ca href=\"/A002113/b002113.txt\"\u003eList of first 19999 palindromes: Table of n, a(n) for n = 1..19999\u003c/a\u003e",
				"Hunki Baek, Sejeong Bang, Dongseok Kim, Jaeun Lee, \u003ca href=\"http://arxiv.org/abs/1412.2426\"\u003eA bijection between aperiodic palindromes and connected circulant graphs\u003c/a\u003e, arXiv:1412.2426 [math.CO], 2014.",
				"William D. Banks, Derrick N. Hart, Mayumi Sakata, \u003ca href=\"http://dx.doi.org/10.4310/MRL.2004.v11.n6.a10\"\u003eAlmost all palindromes are composite\u003c/a\u003e, Math. Res. Lett., 11 No. 5-6 (2004), 853-868.",
				"William D. Banks, \u003ca href=\"http://arxiv.org/abs/1508.04721\"\u003eEvery natural number is the sum of forty-nine palindromes\u003c/a\u003e, arXiv:1508.04721 [math.NT], 2015; \u003ca href=\"https://www.emis.de/journals/INTEGERS/papers/q3/q3.Abstract.html\"\u003eIntegers\u003c/a\u003e, 16 (2016), article A3.",
				"Javier Cilleruelo and Florian Luca, \u003ca href=\"http://arxiv.org/abs/1602.06208v1\"\u003eEvery positive integer is a sum of three palindromes\u003c/a\u003e, arXiv: 1602.06208 [math.NT], 2016.",
				"Javier Cilleruelo, Florian Luca and Lewis Baxter, \u003ca href=\"http://arxiv.org/abs/1602.06208v2\"\u003eEvery positive integer is a sum of three palindromes\u003c/a\u003e, arXiv: 1602.06208 [math.NT], 2017, \u003ca href=\"https://doi.org/10.1090/mcom/3221\"\u003eMath. Comp., published electronically: August 15, 2017.",
				"Patrick De Geest, \u003ca href=\"http://www.worldofnumbers.com/\"\u003eWorld of Numbers\u003c/a\u003e",
				"Phakhinkon Phunphayap, Prapanpong Pongsriiam, \u003ca href=\"https://arxiv.org/abs/1803.09621\"\u003eReciprocal sum of palindromes\u003c/a\u003e, arXiv:1803.00161 [math.CA], 2018.",
				"Simon Plouffe, \u003ca href=\"http://www.lacim.uqam.ca/%7Eplouffe/articles/MasterThesis.pdf\"\u003eApproximations de séries génératrices et quelques conjectures\u003c/a\u003e, Dissertation, Université du Québec à Montréal, 1992.",
				"Simon Plouffe, \u003ca href=\"http://www.lacim.uqam.ca/%7Eplouffe/articles/FonctionsGeneratrices.pdf\"\u003e1031 Generating Functions and Conjectures\u003c/a\u003e, Université du Québec à Montréal, 1992.",
				"Prapanpong Pongsriiam, Kittipong Subwattanachai, \u003ca href=\"http://ijmcs.future-in-tech.net/14.1/R-Pongsriiam.pdf\"\u003eExact Formulas for the Number of Palindromes up to a Given Positive Integer\u003c/a\u003e, Intl. J. of Math. Comp. Sci. (2019) 14:1, 27-46.",
				"E. A. Schmidt, \u003ca href=\"http://eric-schmidt.com/eric/palindrome/index.html\"\u003ePositive Integer Palindromes\u003c/a\u003e [broken link]",
				"Eric Weisstein's World of Mathematics, \u003ca href=\"http://mathworld.wolfram.com/PalindromicNumber.html\"\u003ePalindromic Number\u003c/a\u003e",
				"Wikipedia, \u003ca href=\"http://www.wikipedia.org/wiki/Palindromic_number\"\u003ePalindromic number\u003c/a\u003e",
				"\u003ca href=\"/index/Pac#palindromes\"\u003eIndex entries for sequences related to palindromes\u003c/a\u003e",
				"\u003ca href=\"/index/Cor#core\"\u003eIndex entries for \"core\" sequences\u003c/a\u003e"
			],
			"formula": [
				"A136522(a(n)) = 1.",
				"a(n+1) = A262038(a(n)+1). - _M. F. Hasler_, Sep 09 2015"
			],
			"maple": [
				"read transforms; t0:=[]; for n from 0 to 2000 do if digrev(n) = n then t0:=[op(t0),n]; fi; od: t0;",
				"# Alternatively, to get all palindromes with \u003c= N digits in the list \"Res\":",
				"N:=5;",
				"Res:= $0..9:",
				"for d from 2 to N do",
				"  if d::even then",
				"    m:= d/2;",
				"    Res:= Res, seq(n*10^m + digrev(n),n=10^(m-1)..10^m-1);",
				"  else",
				"    m:= (d-1)/2;",
				"    Res:= Res, seq(seq(n*10^(m+1)+y*10^m+digrev(n),y=0..9),n=10^(m-1)..10^m-1);",
				"  fi",
				"od: Res:=[Res]: # _Robert Israel_, Aug 10 2014",
				"# A variant: Gets all base-10 palindromes with exactly d digits, in the list \"Res\"",
				"d:=4:",
				"if d=1 then Res:= [$0..9]:",
				"elif d::even then",
				"    m:= d/2:",
				"    Res:= [seq(n*10^m + digrev(n), n=10^(m-1)..10^m-1)]:",
				"else",
				"    m:= (d-1)/2:",
				"    Res:= [seq(seq(n*10^(m+1)+y*10^m+digrev(n), y=0..9), n=10^(m-1)..10^m-1)]:",
				"fi:",
				"Res; # _N. J. A. Sloane_, Oct 18 2015",
				"isA002113 := proc(n)",
				"    simplify(digrev(n) = n) ;",
				"end proc: # _R. J. Mathar_, Sep 09 2015"
			],
			"mathematica": [
				"palQ[n_Integer, base_Integer] := Module[{idn = IntegerDigits[n, base]}, idn == Reverse[idn]]; (* then to generate any base-b sequence for 1 \u003c b \u003c 37, replace the 10 in the following instruction with b: *) Select[Range[0, 1000], palQ[#, 10] \u0026]",
				"base10Pals = {0}; r = 2; Do[Do[AppendTo[base10Pals, n * 10^(IntegerLength[n] - 1) + FromDigits@Rest@Reverse@IntegerDigits[n]], {n, 10^(e - 1), 10^e - 1}]; Do[AppendTo[base10Pals, n * 10^IntegerLength[n] + FromDigits@Reverse@IntegerDigits[n]], {n, 10^(e - 1), 10^e - 1}], {e, r}]; base10Pals (* _Arkadiusz Wesolowski_, May 04 2012 *)",
				"nthPalindromeBase[n_, b_] := Block[{q = n + 1 - b^Floor[Log[b, n + 1 - b^Floor[Log[b, n/b]]]], c = Sum[Floor[Floor[n/((b + 1) b^(k - 1) - 1)]/(Floor[n/((b + 1) b^(k - 1) - 1)] - 1/b)] - Floor[Floor[n/(2 b^k - 1)]/(Floor[n/(2 b^k - 1)] - 1/ b)], {k, Floor[Log[b, n]]}]}, Mod[q, b] (b + 1)^c * b^Floor[Log[b, q]] + Sum[Floor[Mod[q, b^(k + 1)]/b^k] b^(Floor[Log[b, q]] - k) (b^(2 k + c) + 1), {k, Floor[Log[b, q]]}]] (* after the work of Eric A. Schmidt, works for all integer bases b \u003e 2 *)",
				"Array[nthPalindromeBase[#, 10] \u0026, 61, 0] (* please note that Schmidt uses a different, a more natural and intuitive offset, that of a(1) = 1. - _Robert G. Wilson v_, Sep 22 2014 and modified Nov 28 2014 *)",
				"Select[Range[10^3], PalindromeQ] (* _Michael De Vlieger_, Nov 27 2017 *)"
			],
			"program": [
				"(PARI) is_A002113(n)={Vecrev(n=digits(n))==n} \\\\ _M. F. Hasler_, Nov 17 2008, updated Apr 26 2014, Jun 19 2018",
				"(PARI) is(n)=n=digits(n);for(i=1,#n\\2,if(n[i]!=n[#n+1-i],return(0))); 1 \\\\ _Charles R Greathouse IV_, Jan 04 2013",
				"(PARI) a(n)={my(d,i,r);r=vector(#digits(n-10^(#digits(n\\11)))+#digits(n\\11));n=n-10^(#digits(n\\11));d=digits(n);for(i=1,#d,r[i]=d[i];r[#r+1-i]=d[i]);sum(i=1,#r,10^(#r-i)*r[i])} \\\\ _David A. Corneth_, Jun 06 2014",
				"(PARI) \\\\ recursive--feed an element a(n) and it gives a(n+1)",
				"nxt(n)={my(d=digits(n));i=(#d+1)\\2;while(i\u0026\u0026d[i]==9,d[i]=0;d[#d+1-i]=0;i--);if(i,d[i]++;d[#d+1-i]=d[i],d=vector(#d+1);d[1]=d[#d]=1);sum(i=1,#d,10^(#d-i)*d[i])} \\\\ _David A. Corneth_, Jun 06 2014",
				"(PARI) \\\\ feed a(n), returns n.",
				"inv(n)={my(d=digits(n));q=ceil(#d/2);sum(i=1,q,10^(q-i)*d[i])+10^floor(#d/2)} \\\\ _David A. Corneth_, Jun 18 2014",
				"(PARI) inv_A002113(P)={P\\(P=10^(logint(P+!P,10)\\/2))+P} \\\\ index n of palindrome P = a(n), much faster than above: no sum is needed. - _M. F. Hasler_, Sep 09 2018",
				"(PARI) A002113(n,L=logint(n,10))=(n-=L=10^max(L-(n\u003c11*10^(L-1)),0))*L+fromdigits(Vecrev(digits(if(n\u003cL,n,n\\10)))) \\\\ _M. F. Hasler_, Sep 11 2018",
				"(Python)# A002113.py # edited by _M. F. Hasler_, Jun 19 2018",
				"def A002113_list(nMax):",
				"  mlist=[]",
				"  for n in range(nMax+1)",
				"     mstr=str(n)",
				"     if mstr==mstr[::-1]:",
				"        mlist.append(n)",
				"  return(mlist)",
				"(Haskell)",
				"  a002113 n = a002113_list !! (n-1)",
				"  a002113_list = filter ((== 1) . a136522) [1..] -- _Reinhard Zumkeller_, Oct 09 2011",
				"(Haskell)",
				"  import Data.List.Ordered (union)",
				"  a002113_list = union a056524_list a056525_list -- _Reinhard Zumkeller_, Jul 29 2015, Dec 28 2011",
				"(Python)",
				"from itertools import chain",
				"A002113 = sorted(chain(map(lambda x:int(str(x)+str(x)[::-1]),range(1,10**3)),map(lambda x:int(str(x)+str(x)[-2::-1]), range(10**3)))) # _Chai Wah Wu_, Aug 09 2014",
				"(MAGMA) [n: n in [0..600] | Intseq(n, 10) eq Reverse(Intseq(n, 10))]; // _Vincenzo Librandi_, Nov 03 2014",
				"(Sage)",
				"[n for n in (0..515) if Word(n.digits()).is_palindrome()] # _Peter Luschny_, Sep 13 2018",
				"(GAP) Filtered([0..550],n-\u003eListOfDigits(n)=Reversed(ListOfDigits(n))); # _Muniru A Asiru_, Mar 08 2019",
				"(Scala) def palQ(n: Int, b: Int = 10): Boolean = n - Integer.parseInt(n.toString.reverse) == 0",
				"(0 to 999).filter(palQ(_)) // _Alonso del Arte_, Nov 10 2019"
			],
			"xref": [
				"Palindromes in bases 2 through 11: A006995 and A057148, A014190 and A118594, A014192 and A118595, A029952 and A118596, A029953 and A118597, A029954 and A118598, A029803 and A118599, A029955 and A118600, this sequence, A029956. Also A262065 (base 60), A262069 (subsequence).",
				"Palindromic primes: A002385. Palindromic nonprimes: A032350.",
				"Palindromic-pi: A136687.",
				"Cf. A029742 (complement), A086862 (first differences).",
				"Palindromic floor function: A261423, also A261424. Palindromic ceiling: A262038.",
				"Union of A056524 and A056525.",
				"Cf. A004086 (read n backwards), A064834, A136522 (characteristic function), A178788.",
				"Ways to write n as a sum of three palindromes: A261132, A261422.",
				"Minimal number of palindromes that add to n using greedy algorithm: A088601.",
				"Minimal number of palindromes that add to n: A261675.",
				"Subsequence of A061917 and A221221.",
				"Subsequence: A110745."
			],
			"keyword": "nonn,base,easy,nice,core",
			"offset": "1,3",
			"author": "_N. J. A. Sloane_",
			"references": 521,
			"revision": 296,
			"time": "2019-12-07T12:31:01-05:00",
			"created": "1991-04-30T03:00:00-04:00"
		},
		{
			"number": 269303,
			"data": "0,1,2,3,4,5,6,8,10,13,19,26,37,69,77,81,214,242,255,900,1113,1833,3166,3566,4753,4849,4869,5005,7372,7702,10240,16100,18972,28574,33815,37820,70457,89482",
			"name": "Numbers n such that (266*10^n+1)/3 is prime.",
			"comment": [
				"Numbers n such that digits 88 followed by n-1 occurrences of digit 6 followed by the digit 7 is prime (see Example section).",
				"a(39) \u003e 10^5."
			],
			"link": [
				"Makoto Kamada, \u003ca href=\"https://stdkmd.net/nrr/prime/primedifficulty.txt\"\u003eSearch for 886w7.\u003c/a\u003e"
			],
			"example": [
				"6 is in this sequence because (266*10^n+1)/3 = 88666667 is prime.",
				"Initial terms and primes associated:",
				"a(1)  = 0,    89;",
				"a(2)  = 1,    887;",
				"a(3)  = 2,    8867;",
				"a(4)  = 3,    88667;",
				"a(5)  = 4,    886667;",
				"a(6)  = 5,    8866667;",
				"a(7)  = 6,    88666667;",
				"a(8)  = 8,    8866666667;",
				"a(9)  = 10,   886666666667;",
				"a(10) = 13,   886666666666667, etc."
			],
			"mathematica": [
				"Select[Range[0, 100000], PrimeQ[(266*10^#+1)/3] \u0026]"
			],
			"program": [
				"(MAGMA) [n: n in [0..220] | IsPrime((266*10^n+1) div 3)]; // _Vincenzo Librandi_, Feb 23 2016",
				"(PARI) is(n)=ispseudoprime((266*10^n+1)/3) \\\\ _Charles R Greathouse IV_, Feb 16 2017"
			],
			"xref": [
				"Cf. A056654, A268448."
			],
			"keyword": "nonn,more",
			"offset": "1,3",
			"author": "_Robert Price_, Feb 22 2016",
			"references": 504,
			"revision": 11,
			"time": "2019-01-17T13:44:08-05:00",
			"created": "2016-02-24T13:03:27-05:00"
		},
		{
			"number": 270613,
			"data": "1,2,3,4,7,10,24,25,29,34,35,37,46,49,88,103,290,381,484,696,751,886,999,1750,5062,6214,9740,12558,16551,24674,28600,37427,48032,61991,70148,72516,99441,179656",
			"name": "Numbers k such that (68*10^k + 7)/3 is prime.",
			"comment": [
				"Numbers such that the digits 22 followed by k-1 occurrences of the digit 6 followed by the digit 9 is prime (see Example section).",
				"a(39) \u003e 2*10^5."
			],
			"link": [
				"Makoto Kamada, \u003ca href=\"https://stdkmd.net/nrr/prime/primedifficulty.txt\"\u003eSearch for 226w9.\u003c/a\u003e"
			],
			"example": [
				"3 is in this sequence because (68*10^3+7)/3 = 22669 is prime.",
				"Initial terms and primes associated:",
				"a(1) = 1, 229;",
				"a(2) = 2, 2269;",
				"a(3) = 3, 22669;",
				"a(4) = 4, 226669;",
				"a(5) = 7, 226666669, etc."
			],
			"mathematica": [
				"Select[Range[0, 100000], PrimeQ[(68*10^# + 7)/3] \u0026]"
			],
			"program": [
				"(PARI) lista(nn) = for(n=1, nn, if(ispseudoprime((68*10^n + 7)/3), print1(n, \", \"))); \\\\ _Altug Alkan_, Mar 20 2016"
			],
			"xref": [
				"Cf. A056654, A268448, A269303, A270339."
			],
			"keyword": "nonn,more,changed",
			"offset": "1,2",
			"author": "_Robert Price_, Mar 20 2016",
			"ext": [
				"a(38) from _Robert Price_, Jan 16 2020"
			],
			"references": 500,
			"revision": 12,
			"time": "2020-01-16T09:19:55-05:00",
			"created": "2016-03-20T12:44:24-04:00"
		},
		{
			"number": 270831,
			"data": "1,2,3,4,5,7,23,29,37,39,40,89,115,189,227,253,301,449,533,607,969,1036,1207,1407,1701,3493,7147,11342,21638,22327,25575,25648,34079,39974,47719,49913,74729,100737,103531,168067",
			"name": "Numbers k such that (7*10^k + 71)/3 is prime.",
			"comment": [
				"For n\u003e1, numbers such that the digit 2 followed by n-2 occurrences of the digit 3 followed by the digits 57 is prime (see Example section).",
				"a(41) \u003e 2*10^5."
			],
			"link": [
				"Makoto Kamada, \u003ca href=\"https://stdkmd.net/nrr/prime/primedifficulty.txt\"\u003eSearch for 23w57.\u003c/a\u003e"
			],
			"example": [
				"3 is in this sequence because (7*10^3 + 71)/3 = 2357 is prime.",
				"Initial terms and primes associated:",
				"a(1) = 1, 47;",
				"a(2) = 2, 257;",
				"a(3) = 3, 2357;",
				"a(4) = 4, 23357;",
				"a(5) = 5, 233357, etc."
			],
			"mathematica": [
				"Select[Range[0, 100000], PrimeQ[(7*10^# + 71)/3] \u0026]"
			],
			"program": [
				"(PARI) lista(nn) = {for(n=1, nn, if(ispseudoprime((7*10^n + 71)/3), print1(n, \", \"))); } \\\\ _Altug Alkan_, Mar 23 2016"
			],
			"xref": [
				"Cf. A056654, A268448, A269303, A270339, A270613."
			],
			"keyword": "nonn",
			"offset": "1,2",
			"author": "_Robert Price_, Mar 23 2016",
			"ext": [
				"a(38)-a(40) from _Robert Price_, May 21 2018"
			],
			"references": 498,
			"revision": 12,
			"time": "2019-01-17T13:44:08-05:00",
			"created": "2016-03-25T07:45:51-04:00"
		},
		{
			"number": 270890,
			"data": "0,1,2,3,4,5,6,10,24,33,34,35,45,52,56,62,65,103,166,424,886,1418,1825,4895,5715,7011,7810,9097,12773,14746,20085,25359,27967,46629,48507,68722,74944",
			"name": "Numbers n such that (8*10^n+49)/3 is prime.",
			"comment": [
				"For n\u003e2, numbers such that the digit 2 followed by n-3 occurrences of the digit 6 followed by the digits 83 is prime (see Example section).",
				"a(38) \u003e 10^5."
			],
			"link": [
				"Makoto Kamada, \u003ca href=\"https://stdkmd.net/nrr/prime/primedifficulty.txt\"\u003eSearch for 26w83.\u003c/a\u003e"
			],
			"example": [
				"3 is in this sequence because (8*10^3+49)/3 = 2683 is prime.",
				"Initial terms and primes associated:",
				"a(1) = 0, 19;",
				"a(2) = 1, 43;",
				"a(3) = 2, 283;",
				"a(4) = 3, 2683;",
				"a(5) = 4, 26683;",
				"a(6) = 5, 266683, etc."
			],
			"mathematica": [
				"Select[Range[0, 100000], PrimeQ[(8*10^#+49)/3] \u0026]"
			],
			"program": [
				"(PARI) is(n)=isprime((8*10^n+49)/3) \\\\ _Charles R Greathouse IV_, Feb 16 2017"
			],
			"xref": [
				"Cf. A056654, A268448, A269303, A270339, A270613, A270831."
			],
			"keyword": "nonn,more",
			"offset": "1,3",
			"author": "_Robert Price_, Mar 25 2016",
			"references": 497,
			"revision": 8,
			"time": "2019-01-17T13:44:08-05:00",
			"created": "2016-03-25T23:02:09-04:00"
		},
		{
			"number": 270929,
			"data": "1,2,3,4,15,20,24,32,38,40,63,93,104,194,208,514,535,600,928,1300,1485,1780,2058,3060,3356,3721,6662,11552,15482,23000,27375,34748,57219,61251,85221,99656,103214,103244",
			"name": "Numbers k such that (16*10^k - 31)/3 is prime.",
			"comment": [
				"For k\u003e1, numbers such that the digit 5 followed by k-2 occurrences of the digit 3 followed by the digits 23 is prime (see Example section).",
				"a(39) \u003e 2*10^5."
			],
			"link": [
				"Makoto Kamada, \u003ca href=\"https://stdkmd.net/nrr/prime/primedifficulty.txt\"\u003eSearch for 53w23.\u003c/a\u003e"
			],
			"example": [
				"3 is in this sequence because (16*10^3 - 31)/3 = 5323 is prime.",
				"Initial terms and primes associated:",
				"a(1) = 1, 43;",
				"a(2) = 2, 523;",
				"a(3) = 3, 5323;",
				"a(4) = 4, 53323;",
				"a(5) = 15, 5333333333333323;",
				"a(6) = 20, 533333333333333333323, etc."
			],
			"mathematica": [
				"Select[Range[0, 100000], PrimeQ[(16*10^# - 31)/3] \u0026]"
			],
			"program": [
				"(PARI) isok(n) = ispseudoprime((16*10^n - 31)/3); \\\\ _Michel Marcus_, Mar 26 2016"
			],
			"xref": [
				"Cf. A056654, A268448, A269303, A270339, A270613, A270831, A270890."
			],
			"keyword": "nonn,base,more",
			"offset": "1,2",
			"author": "_Robert Price_, Mar 26 2016",
			"ext": [
				"a(37)-a(38) from _Robert Price_, Mar 03 2019"
			],
			"references": 496,
			"revision": 13,
			"time": "2019-03-03T10:44:11-05:00",
			"created": "2016-03-26T22:07:11-04:00"
		}
	]
}"""