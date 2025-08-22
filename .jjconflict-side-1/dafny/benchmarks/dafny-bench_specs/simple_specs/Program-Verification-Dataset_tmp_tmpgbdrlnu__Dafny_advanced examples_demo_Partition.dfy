// SPEC
method Partition(a: array<int>) returns (lo: int, hi: int)
 modifies a
 ensures 0 <= lo <= hi <= a.Length
 ensures forall x | 0 <= x < lo :: a[x] < 0
 ensures forall x | lo <= x < hi :: a[x] == 0
 ensures forall x | hi <= x < a.Length :: a[x] > 0
{
}
