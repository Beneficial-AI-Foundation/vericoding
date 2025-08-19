//IMPL
method mfirstCero(v:array<int>) returns (i:int)
/* code modified by LLM (iteration 3): removed redundant null check since array<int> is non-null type */
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0 
{
    i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant forall j:: 0 <= j < i ==> v[j] != 0
    {
        if v[i] == 0 {
            return;
        }
        i := i + 1;
    }
}