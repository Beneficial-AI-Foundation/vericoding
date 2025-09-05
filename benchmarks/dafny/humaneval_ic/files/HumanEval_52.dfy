This verification task implements a method to check if all integers in a given list are strictly less than a specified threshold value. The method should return true if and only if every element in the sequence satisfies the threshold condition.

// ======= TASK =======
// Given a list of integers and a threshold integer, determine if all numbers 
// in the list are strictly less than the threshold.

// ======= SPEC REQUIREMENTS =======
predicate BelowThreshold(l: seq<int>, t: int)
{
    forall i :: 0 <= i < |l| ==> l[i] < t
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method CheckBelowThreshold(l: seq<int>, t: int) returns (result: bool)
    ensures result == BelowThreshold(l, t)
{
    result := forall i :: 0 <= i < |l| ==> l[i] < t;
}
