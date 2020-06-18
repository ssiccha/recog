gap> testFunction := function(G, eps, N)
>     C := ThreeCycleCandidates(G, eps, N, IsOne, EQ);
>     if C <> fail then
>         for i in [1 .. 10] do
>             BolsteringElements(G, PseudoRandom(C), eps, N, IsOne, EQ);
>         od;
>     fi;
> end;;
gap> testGroups := [
>     SymmetricGroup(10),
>     SymmetricGroup(100),
>     AlternatingGroup(10),
>     AlternatingGroup(100),
>     DihedralGroup(IsPermGroup,10),
>     DihedralGroup(IsPcGroup, 10),
>     DihedralGroup(IsPermGroup, 2000),
>     DihedralGroup(IsPcGroup, 2000),
>     Group(List(GeneratorsOfGroup(SymmetricGroup(10)), x -> PermutationMat(x, 10, GF(9)))),
>     Group(List(GeneratorsOfGroup(SymmetricGroup(10)), x -> PermutationMat(x, 10, GF(9))))^PseudoRandom(GL(10,9)),
>     SL(3,5)
> ];;
gap> for G in testGroups do 
>     #Print(Order(G), " \n");
>     testFunction(G, 1/100, 100);
> od;
gap> 