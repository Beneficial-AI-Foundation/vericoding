//ATOM

ghost function SetProduct(s : set<int>) : int
{
  if s == {} then 1
  else var x :| x in s; 
     x * SetProduct(s - {x})
}

/* 
 * This is necessary because, when we add one element, we need to make sure
 * that the product of the new set, as a whole, is the same as the product
 * of the old set times the new element.
 */


//IMPL 
method UniqueProduct (arr: array<int>) returns (product: int)
  ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
  var seen: set<int> := {};
  product := 1;
  
  /* code modified by LLM (iteration 4): Fixed invariants to properly handle duplicates by tracking seen as subset of array elements rather than exact correspondence with index range */
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant seen <= (set j | 0 <= j < arr.Length :: arr[j])
    invariant product == SetProduct(seen)
    invariant seen == (set j | 0 <= j < i && arr[j] !in (set k | 0 <= k < j :: arr[k]) :: arr[j])
  {
    if arr[i] !in seen {
      seen := seen + {arr[i]};
      product := product * arr[i];
    }
    i := i + 1;
  }
}