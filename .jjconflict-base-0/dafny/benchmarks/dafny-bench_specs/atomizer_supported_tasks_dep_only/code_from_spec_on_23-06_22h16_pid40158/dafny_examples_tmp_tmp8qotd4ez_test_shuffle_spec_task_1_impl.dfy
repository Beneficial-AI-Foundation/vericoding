//IMPL random
method random(a: int, b: int) returns (r: int)
  ensures a <= b ==> a <= r <= b
{
  /* code modified by LLM (iteration 4): Fixed implementation with proper value assignment */
  if a <= b {
    r := a; // Setting r to a ensures a <= r, and since a <= b, we also have r <= b
    assert a <= r <= b; // This should verify given a <= b and r == a
  } else {
    r := 0; // When a > b, the postcondition is vacuously true (antecedent is false)
  }
}

//ATOM eqMultiset_t
predicate eqMultiset_t<T>(s1: multiset<T>, s2: multiset<T>)
{
  s1 == s2
}

//ATOM eqMultiset
predicate eqMultiset(s1: multiset<int>, s2: multiset<int>)
{
  s1 == s2
}

//ATOM swap
method swap<T>(arr: array<T>, i: int, j: int)
  requires 0 <= i < arr.Length
  requires 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j])
  ensures arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
{
  var temp := arr[i];
  arr[i] := arr[j];
  arr[j] := temp;
}

//ATOM getAllShuffledDataEntries
method getAllShuffledDataEntries() returns (entries: seq<int>)
  ensures |entries| >= 0
{
  entries := [];
}

//ATOM set_of_seq
function set_of_seq<T>(s: seq<T>): set<T>
{
  set x | x in s
}

//ATOM in_set_of_seq
predicate in_set_of_seq<T>(x: T, s: seq<T>)
{
  x in set_of_seq(s)
}

//ATOM subset_set_of_seq
predicate subset_set_of_seq<T>(s1: seq<T>, s2: seq<T>)
{
  set_of_seq(s1) <= set_of_seq(s2)
}

//ATOM getRandomDataEntry
method getRandomDataEntry() returns (entry: int)
{
  entry := 0;
}