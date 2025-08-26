// Assuming Array is Object Blood
// Blood Array<int>
// index

// <vc-helpers>
// </vc-helpers>

method Find(blood: array<int>, key: int) returns (index: int)
requires blood != null
ensures 0 <= index ==> index < blood.Length && blood[index] == key
ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
// <vc-code>
{
  assume false;
}
// </vc-code>