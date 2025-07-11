// ATOM 
ghost method M1()
{

//	assert 1 == 2;
	assume 1 == 2;
}


// ATOM 

lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
	requires C == A*B
	ensures C <= A && C <= B
{}


// ATOM 

lemma BothSetsAreSubsetsOfTheirUnion(A: set, B: set, C: set)
	requires C == A+B
	ensures A <= C && B <= C
{}

const s0 := {3,8,1}


const s0 := {3,8,1}
//var s2 := {4,5}

// ATOM 
//var s2 := {4,5}

lemma M2()
{
	var s1 := {2,4,6,8};
	//s0 := {4,1,2};
	s1 := {};
}


// ATOM 

lemma TheEmptySetIsASubsetOfAnySet(A: set, B: set)
	requires A == {}
	ensures A <= B // same as writing: B >= A
{}

	ensures A <= B // same as writing: B >= A
{}

// ATOM 

lemma AnySetIsASubsetOfItself(A: set)
	ensures A <= A
{}


// ATOM 

lemma TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set, B: set, C: set, D: set)
	requires C == A*B && D == A+B
	ensures C <= D
{
}




