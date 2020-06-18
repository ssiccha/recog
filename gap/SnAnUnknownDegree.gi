#
ThreeCycleCandidates := function()
end;

#######
# G: the group to recognize
# c: possibly a 3-cycle
# returns a list of group elements. If G is isomorphic to an alternating or
# symmetric group and c is a 3-cycle, then this function returns a list of
# bolstering elements with respect to c.
BindGlobal("BolsteringElements",
function(G, c, eps, N, groupIsOne, groupIsEq)
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
