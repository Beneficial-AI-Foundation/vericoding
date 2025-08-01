//IMPL
method intersect (a: array<real>, b: array<real>) returns (ret: array<real>)
    ensures ret.Length < a.Length && ret.Length < b.Length;
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> if a[i] == b[j] then exists k :: 0 <= k < ret.Length && ret[k] == a[i] else ! (exists k :: 0 <= k < ret.Length && ret[k] == a[i]);
{
    var temp := new real[if a.Length < b.Length then a.Length else b.Length];
    var count := 0;
    
    for i := 0 to a.Length
        invariant 0 <= count <= i
        invariant count < temp.Length
        invariant forall x :: 0 <= x < count ==> exists y :: 0 <= y < i && a[y] == temp[x]
        invariant forall x :: 0 <= x < count ==> exists y :: 0 <= y < b.Length && b[y] == temp[x]
        invariant forall x, y :: 0 <= x < i && 0 <= y < b.Length && a[x] == b[y] ==> exists z :: 0 <= z < count && temp[z] == a[x]
    {
        var found := false;
        for j := 0 to b.Length
            invariant found <==> exists y :: 0 <= y < j && a[i] == b[y]
        {
            if a[i] == b[j] {
                found := true;
                break;
            }
        }
        
        if found {
            var alreadyInTemp := false;
            for k := 0 to count
                invariant alreadyInTemp <==> exists z :: 0 <= z < k && temp[z] == a[i]
            {
                if temp[k] == a[i] {
                    alreadyInTemp := true;
                    break;
                }
            }
            
            if !alreadyInTemp {
                temp[count] := a[i];
                count := count + 1;
            }
        }
    }
    
    ret := new real[count];
    for i := 0 to count
        invariant forall x :: 0 <= x < i ==> ret[x] == temp[x]
    {
        ret[i] := temp[i];
    }
}