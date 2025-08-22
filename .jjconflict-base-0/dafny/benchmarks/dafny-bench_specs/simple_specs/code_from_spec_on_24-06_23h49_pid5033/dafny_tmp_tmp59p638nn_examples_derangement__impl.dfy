//IMPL derangement_method
predicate permutation(links: seq<int>)
{
  |links| > 0 ==> (forall i :: 0 <= i < |links| ==> 0 <= links[i] < |links|) &&
  (forall i :: 0 <= i < |links| ==> exists j :: 0 <= j < |links| && links[j] == i)
}

predicate derangement(links: seq<int>)
{
  forall i :: 0 <= i < |links| ==> links[i] != i
}

predicate distinct(links: seq<int>)
{
  forall i, j :: 0 <= i < j < |links| ==> links[i] != links[j]
}

method ProcessDerangement(links: seq<int>) returns (result: bool)
  requires |links| > 0
  requires permutation(links)
  requires derangement(links)
  requires distinct(links)
  ensures result == true
{
  result := true;
}