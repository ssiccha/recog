# Input: Group G, upper error bound eps, upper degree bound N
#
# The following algorithm constructs a set of possible 3-cycles. It is based
# on the simple observation that the product of two involutions t1, t2, which
# only move one common point, squares to a 3-cycle.
#
# Returns a an iterator
BindGlobal("ThreeCycleCandidatesIterator",
    function(G, eps, N, groupIsOne, groupIsEq)
    # The local variables are explained in more detail in
    # ThreeCycleCandidatesNextIterator
    local
        # integers, number of iterations
        M,B,T,C,logInt2N,
        # integer, prime, loop variable
        p;
    # 1. Step: Initialization
    # Constants
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
    logInt2N := LogInt(N, 2);
    # Counters
    # We initialize nrTriedConjugates to C such that, ... FIXME flips
    # immediately
    nrThreeCycleCandidates := 0,
    nrTriedConjugates := C,
    nrInvolutions := 0,
    return ThreeCycleCandidatesNextIterator();
    # FIXME move into ThreeCycleCandidatesNextIterator. If Iteration is
    # finished return fail. Then the main loop can return until `t ==
    # fail`.
    iter!.nrInvolutions >= iter!.B
        and (iter!.nrTriedConjugates >= C
            or iter!.nrThreeCycleCandidates >= iter!.T);
end);

# Either return an element of G or fail or NeverApplicable
# nrInvolutions counts the constructed involutions t_i in 2. + 3. Step
# nrTriedConjugates counts the elements c in 4. Step that we use to conjugate the current involution t_i
# nrThreeCycleCandidates counts the size of the set Gamma_i in 4. Step for the current involution t_i
# TODO: take care of duplicate candidates?
BindGlobal("ThreeCycleCandidatesNextIterator",
function(iter)
    local
        # integer, loop variable
        a,
        # elements, in G
        r,t,tPower,tPowerOld,c;
    if IsDoneIterator(iter) then return fail; fi;
    # 2. + 3. Step : Involution
    # Check if we either tried enough conjugates or
    # constructed enough three cycle candidates for the current involution t.
    # If this is the case, we need to construct the next involution
    if iter!.t = fail or iter!.nrTriedConjugates >= iter!.C or iter!.nrThreeCycleCandidates >= iter!.T then
        r := PseudoRandom(iter!.G);
        a := 0;
        tPower := r^iter!.M;
        # Invariant: tPower = (r ^ M) ^ (2 ^ a)
        repeat
            a := a + 1;
            tPowerOld := tPower;
            tPower := tPower ^ 2;
        until a = iter!.logInt2N or iter!.groupIsOne(tPower);
        if a = iter!.logInt2N then
            return NeverApplicable;
        fi;
        iter!.t := tPowerOld;
        iter!.nrInvolutions := iter!.nrInvolutions + 1;
        iter!.nrTriedConjugates := 0;
        iter!.nrThreeCycleCandidates := 0;
    fi;
    # 4. + 5. Step : Three Cycle Candidate
    # Try to construct a three cycle candidate via a conjugate of t by
    # using the observation described in the comment above this function.
    iter!.nrTriedConjugates := iter!.nrTriedConjugates + 1;
    c := iter!.t ^ PseudoRandom(iter!.G);
    if not iter!.groupIsEq(iter!.t * c, c * iter!.t) then
        iter!.nrThreeCycleCandidates := iter!.nrThreeCycleCandidates + 1;
        return (iter!.t * c) ^ 2;
    else
        return fail;
    fi;
end);

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
    i := 0;
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
end);

# g: a cycle matching c of a group G
# c: a 3-cycle of a group G
# r: arbitrary element of a group G
# The supports of c and c^(g^2) have exactly one point, say alpha, in common.
# Let phi be an isomorphism from G to a natural alternating or symmetric group.
# This function decides whether alpha is a fixed point of phi(r).
BindGlobal("IsFixedPoint",
function(g, c, r, groupIsOne, groupIsEq)
    local
        # respectively c ^ (g ^ i)
        cg, cg2, cg3, cg4,
        # temporary holder of H1, H2
        temp,
        # (sets of) elements of G
        H1, H2, x1, x2, x3,
        # helper function
        isElmPassingTest;
    # Helper function
    isElmPassingTest := function(x, H, groupIsOne)
        local nrTrivialComm, h;
        nrTrivialComm := 0;
        for h in H do
            if groupIsOne(Comm(x, h)) then
                nrTrivialComm := nrTrivialComm + 1;
            fi;
            if nrTrivialComm >= 2 then
                return false;
            fi;
        od;
        return true;
    end;
    cg := c ^ g;
    cg2 := cg ^ g;
    cg3 := cg2 ^ g;
    cg4 := cg3 ^ g;
    H1 := [ c ^ 2, c ^ cg, ~[2] ^ cg3, ~[3] ^ cg3, ~[4] ^ cg4 ];
    # Test whether an elm of the set X, here called XX, commutes with at least
    # two elements of H1.
    x1 := c ^ r;
    if not isElmPassingTest(x1, H1, groupIsOne) then return false; fi;
    x2 := cg2 ^ r;
    if not isElmPassingTest(x2, H1, groupIsOne) then return false; fi;
    x3 := ((cg2 ^ cg3) ^ cg4) ^ r;
    if not isElmPassingTest(x3, H1, groupIsOne) then return false; fi;
    # Test whether an elm of the set X, here called XX, commutes with at least
    # two elements of H2.
    H2 := [c, cg, ~[2] ^ cg3, ~[3] ^ cg3, ~[4] ^ cg4];
    if not isElmPassingTest(x1, H2, groupIsOne) then return false; fi;
    if not isElmPassingTest(x2, H2, groupIsOne) then return false; fi;
    if not isElmPassingTest(x3, H2, groupIsOne) then return false; fi;
    return true;
end);

# g: a k-cycle matching c of a group G
# c: a 3-cycle of a group G
# r: element of a group G
# W.l.o.g. let g = (1, ..., k) and c = (1, 2, 3).
# If the support of g has at least one point in common with the support of r
# and at least two points of support of g are fixed by r,
# then the algorithm returns a conjugate r^x such that r fixes the points 1, 2
# but not the point 3.
BindGlobal("AdjustCycle",
function(g, c, r, k, groupIsOne, groupIsEq)
    local
        # list of 4 booleans, is point j fixed point
        F,
        # smallest fixed point
        f1,
        # second smallest fixed point
        f2,
        # smallest non-fixed point
        m,
        # integer, loop variable over [1 .. k]
        j,
        # element of G, loop variable
        t,
        # conjugating element
        x;
    F := [false, false, false, false];
    f1 := fail;
    f2 := fail;
    m := fail;
    j := 0;
    t := c ^ (g ^ -3);
    # invariant: t = c ^ (g ^ (j - 3))
    repeat
        j := j + 1;
        t := t ^ g;
        if IsFixedPoint(g, t, r, groupIsOne, groupIsEq) then
            if j <= 4 then
                F[j] := true;
            fi;
            if f1 = fail then
                f1 := j;
            elif f2 = fail then
                f2 := j;
            fi;
        elif m = fail then
            m := j;
        fi;
    until j >= k or (j >= 4 and f1 <> fail and f2 <> fail and m <> fail);
    if f1 = fail or f2 = fail or m =fail then
        return fail;
    fi;
    # case distinction on F as in the table of Algorithm 4.20
    if F[1] then
        if F[2] then
            if F[3] then
                # 1. Case
                x := c ^ ((g * c ^ 2) ^ (m - 3) * c) * c;
            else
                # 2. Case
                x := IsOne(c);
            fi;
        else
            if F[3] then
                if F[4] then
                    # 3. Case
                    x := c ^ g;
                else
                    # 4. Case
                    x := (c ^ 2) ^ g;
                fi;
            else
                # 5. Case
                x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c);
            fi;
        fi;
    else
        if F[2] then
            if F[4] then
                # 6. Case
                x := c ^ (c ^ g);
            else
                if F[3] then
                    # 7. Case
                    x := (c ^ 2) ^ (c ^ g);
                else
                    # 8. Case
                    x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c ^ g);
                fi;
            fi;
        else
            if F[3] then
                # 9. Case
                x := (c ^ 2) ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ 2;
            else
                # 10. Case
                x := c ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ ((g * c ^ 2) ^ (f1 - 3));
            fi;
        fi;
    fi;
    return r^x;
end);
