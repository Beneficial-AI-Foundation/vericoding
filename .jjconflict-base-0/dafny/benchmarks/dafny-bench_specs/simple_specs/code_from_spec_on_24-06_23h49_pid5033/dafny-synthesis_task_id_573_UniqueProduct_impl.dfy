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


//IMPL UniqueProduct
method UniqueProduct (arr: array<int>) returns (product: int)
  ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
  product := 1;
  var processed := {};
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    /* code modified by LLM (iteration 4): Track unique elements from array prefix correctly */
    invariant processed == (set j | 0 <= j < i :: arr[j])
    /* code modified by LLM (iteration 4): Product equals SetProduct of processed unique elements */
    invariant product == SetProduct(processed)
  {
    /* code modified by LLM (iteration 4): Update processed set to include current element */
    var old_processed := processed;
    processed := processed + {arr[i]};
    
    /* code modified by LLM (iteration 4): Only multiply when element is truly new */
    if arr[i] !in old_processed {
      /* code modified by LLM (iteration 4): Use SetProduct property for new elements */
      assert processed == old_processed + {arr[i]};
      assert arr[i] !in old_processed;
      assert SetProduct(processed) == SetProduct(old_processed) * arr[i];
      product := product * arr[i];
    } else {
      /* code modified by LLM (iteration 4): When element already exists, processed set unchanged */
      assert arr[i] in old_processed;
      assert processed == old_processed;
      assert SetProduct(processed) == SetProduct(old_processed);
    }
    
    i := i + 1;
  }
}