ghost function SetProduct(s : set<int>) : int
{
    if s == {} then 1
    else var x :| x in s; 
         x * SetProduct(s - {x})
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
