predicate IsPermutation(links: seq<int>)
{
  (forall i {:trigger links[i]} :: 0 <= i < |links| ==> exists j :: 0 <= j < |links| && links[j] == i)
}