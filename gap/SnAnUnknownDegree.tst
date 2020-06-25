#@local degrees, testGroups, G
# TODO
# - projective
# - exploit isomorphisms to verify BolsteringElements
gap> testFunction := function(G, eps, N)
>     local C, i;
>     C := ThreeCycleCandidates(G, eps, N, IsOne, EQ);
>     if C <> NeverApplicable then
>         for i in [1 .. 10] do
>             BolsteringElements(G, PseudoRandom(C), eps, N, IsOne, EQ);
>         od;
>     fi;
> end;;
gap> degrees := [30, 100, 30, 100, 30, 30, 200, 200, 30, 30, 30];;
gap> testGroups := [
>     SymmetricGroup(10),
>     SymmetricGroup(100),
>     AlternatingGroup(10),
>     AlternatingGroup(100),
>     DihedralGroup(IsPermGroup,10),
>     DihedralGroup(IsPcGroup, 10),
>     DihedralGroup(IsPermGroup, 2000),
>     DihedralGroup(IsPcGroup, 2000),
>     Group(List(
>         GeneratorsOfGroup(SymmetricGroup(10)),
>         x -> ImmutableMatrix(GF(9), PermutationMat(x, 10, GF(9)))
>     )),
>     Group(List(
>         GeneratorsOfGroup(SymmetricGroup(10)),
>         x -> ImmutableMatrix(GF(9), PermutationMat(x, 10, GF(9)))^PseudoRandom(GL(10,9))
>     )),
>     SL(3,5)
> ];;

# ThreeCycleCandidates
gap> for i in [1 .. Length(testGroups)] do 
>     ThreeCycleCandidates(testGroups[i], 1/100, degrees[i], IsOne, EQ);
> od;

# BolsteringElements
gap> for i in [1 .. Length(testGroups)] do 
>     G := testGroups[i];
>     BolsteringElements(G, PseudoRandom(G), 1/100, degrees[i], IsOne, EQ);
> od;
