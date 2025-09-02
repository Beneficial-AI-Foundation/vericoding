//IMPL Find
method Find(blood: array<int>, key: int) returns (index: int)
requires blood != null
ensures 0 <= index ==> index < blood.Length && blood[index] == key
ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
{
    var i := 0;
    while i < blood.Length
        invariant 0 <= i <= blood.Length
        invariant forall k :: 0 <= k < i ==> blood[k] != key
    {
        if blood[i] == key {
            index := i;
            return;
        }
        i := i + 1;
    }
    index := -1;
}