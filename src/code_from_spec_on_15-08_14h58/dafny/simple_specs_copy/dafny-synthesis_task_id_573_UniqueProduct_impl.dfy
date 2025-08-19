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
  var seen := {};
  product := 1;
  
  for i := 0 to arr.Length
    /* code modified by LLM (iteration 2): Fixed invariant to maintain seen as set of unique elements processed so far */
    invariant seen == set j | 0 <= j < i :: arr[j]
    invariant product == SetProduct(seen)
  {
    /* code modified by LLM (iteration 2): Only add element to seen if not already present, maintaining invariant */
    if arr[i] !in seen {
      seen := seen + {arr[i]};
      product := product * arr[i];
    }
  }
}