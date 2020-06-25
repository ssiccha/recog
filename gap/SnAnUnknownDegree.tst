#@local testFunction, permToPermMat, degreesToTest, isos;
#@local nonIsomorphicGroups;
#@local g, c, r, i;
# TODO
# - projective
# - use isomorphisms to verify BolsteringElements
gap> testFunction := function(G, eps, N)
>     local C, i;
>     C := ThreeCycleCandidates(G, eps, N, IsOne, EQ);
>     if C <> NeverApplicable then
>         for i in [1 .. 10] do
>             BolsteringElements(G, PseudoRandom(C), eps, N, IsOne, EQ);
>         od;
>     fi;
> end;;
gap> degreesToTest := [10, 20, 30, 40, 50, 60, 70];;
gap> Append(degreesToTest, Primes{[5 .. 15]});;
# TODO: more non-isomorphic examples
gap> nonIsomorphicGroups := [
>     DihedralGroup(IsPermGroup,10),
>     DihedralGroup(IsPcGroup, 10),
>     DihedralGroup(IsPermGroup, 2000),
>     DihedralGroup(IsPcGroup, 2000),
>     SL(3,5),
> ];;
# isomorphisms into different representations
# TODO
# - on sets
# - on tuples
#   - first comp
#   - diagonal
gap> permToPermMat :=
>   {x, deg, field}
>   ->
>   ImmutableMatrix(field, PermutationMat(x, deg, field));;
gap> # TODO: use permToPermMat with varying degrees and fields
gap> isos := [];;


# ThreeCycleCandidates
gap> for i in [1 .. Length(testGroups)] do
>     ThreeCycleCandidates(testGroups[i], 1/100, degrees[i], IsOne, EQ);
> od;

# BolsteringElements
gap> for i in [1 .. Length(testGroups)] do
>     G := testGroups[i];
>     BolsteringElements(G, PseudoRandom(G), 1/100, degrees[i], IsOne, EQ);
> od;

# IsFixedPoint
# TODO
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (1,2)(4,5,6);;
gap> IsFixedPoint(g,c,r,IsOne,EQ);
true
gap> r := (2,3,4);;
gap> IsFixedPoint(g,c,r,IsOne,EQ);
false

# AdjustCycle
# TODO
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (1,2,3)(5,6);;
gap> AdjustCycle(g, c, r, 8, IsOne, EQ);
(3,4,7)(5,6)
