//IMPL
method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s

ensures min_i >= s 
ensures min_i < e 
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
    min_i := s;
    var i := s + 1;
    
    while i < e
        invariant s <= min_i < i
        invariant i <= e
        invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    {
        if a[i] < a[min_i] {
            min_i := i;
        }
        i := i + 1;
    }
}