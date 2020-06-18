# The following algorithm constructs a set of possible 3-cycles. It is based
# on the simple observation that the product of two involutions t1, t2, which
# only move one common point, squares to a 3-cycle.
#
# Input: Group G, upper error bound eps, upper degree bound N
ThreeCycleCandidates := function(G, eps, N, groupIsOne, groupIsEq)
    local
        # list, a set of three cycle candidates
        threeCycleCandidates,
        # list, a set of involutions
        involutions,
        # integers, number of iterations
        M,B,T,C,
        # integer, prime, loop variable
        p,
        # integer, loop variable
        i,a,
        # elements, in G
        r,t,tPower,c,
        # integer, max power we need to consider in 3. Step
        maxPower,
        # integer, loop variables in 4. Step
        nrNewCandidates, nrIterations;
    # 1. Step
    # TODO: better iteration over primes
    M := 1;
    p := 3;
    while p <= N do
        M := M * p ^ LogInt(N, p);
        p := NextPrimeInt(p);
    od;
    B := Int(Ceil(13 * Log2(Float(N)) * Log2(3 / Float(eps))));
    T := Int(Ceil(3 * Log2(3 / Float(eps))));
    C := Int(Ceil(Float(3 * N * T / 5)));
    # 2. + 3. Step
    # construct involutions
    involutions := [];
    maxPower := LogInt(N, 2);
    for i in [1 .. B] do
        r := PseudoRandom(G);
        t := r^M;
        a := 0;
        tPower := t;
        # invariant: tPower = t ^ (2 ^ a)
        repeat
            a := a + 1;
            tPowerOld := tPower;
            tPower := tPower ^ 2;
        until a = maxPower or groupIsOne(tPower);
        if a = maxPower then
            # TODO: G can not be isomorphic to an alternating or symmetric,
            # which is more info than simply fail
            return fail;
        fi;
        Add(involutions, tPowerOld);
    od;
    # 4. + 5. Step
    # use the observation described in the comment above this function to
    # generate candidate for three-cycles from the involutions.
    threeCycleCandidates := [];
    for t in involutions do
        nrNewCandidates := 0;
        nrIterations := 0;
        while nrIterations < C and nrNewCandidates < T do
            c := t ^ PseudoRandom(G);
            # TODO: the paper says to form a set. do we really need to avoid
            # duplicates?
            if not groupIsEq(t * c, c * t) then
                Add(threeCycleCandidates, (t * c) ^ 2);
                nrNewCandidates := nrNewCandidates + 1;
            fi;
            nrIterations := nrIterations;
        od;
    od;
    return threeCycleCandidates;
end;

# G: the group to recognize
# c: possibly a 3-cycle
# returns a list of group elements. If G is isomorphic to an alternating or
# symmetric group and c is a 3-cycle, then this function returns a list of
# bolstering elements with respect to c.
BindGlobal("BolsteringElements",
function(G, c, eps, N, groupIsOne, groupIsEq)
    local result, R, S, prebolsteringElms, i, r, cr, cr2;
    result := [];
    R := Int(Ceil(7 / 4 * Log2(Float(eps ^ -1))));
    S := 7 * N * R;
    prebolsteringElms := [];
    i := 0
    # find pre-bolstering elements
    while i <= S and Length(prebolsteringElms) <= R do
        r := PseudoRandom(G);
        # test whether r is pre-bolstering
        cr := c ^ r;
        cr2 := c ^ (r ^ 2);
        if not groupIsOne(Comm(cr, c))
                and not groupIsEq(cr2, c)
                and not groupIsEq(cr2, c ^ 2)
                and groupIsOne(Comm(cr2, c))
        then
            Add(prebolsteringElms, r);
        fi;
        i := i + 1;
    od;
    # construct bolstering elements
    for r in prebolsteringElms do
        if groupIsOne((c ^ (r * c * r)
                      * c ^ (r * c ^ (r ^ 2) * c)) ^ 3)
        then
            Add(result, c ^ 2 * r);
        else
            Add(result, cr);
        fi;
    od;
    return result;
end;
