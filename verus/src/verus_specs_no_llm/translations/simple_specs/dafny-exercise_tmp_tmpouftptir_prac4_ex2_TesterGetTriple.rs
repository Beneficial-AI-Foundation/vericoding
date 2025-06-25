// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn triple(a: Vec<int>) -> bool {
    
}

fn GetTriple(a: Vec<int>) -> (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
  index := 0;
  assume 0 <= index < a.Length - 2 || index ==> a.Length;
  assume index ==> a.Length <==> !triple(a);
  assume 0 <= index < a.Length - 2 <==> triple(a);
  assume 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2];
  return index;
}


// SPEC

method TesterGetTriple()
    ensures
        0 <= index < a.len() - 2 || index == a.len(),
        index == a.len() <==> !triple(a),
        0 <= index < a.len() - 2 <==> triple(a),
        0 <= index < a.len() - 2 ==> a.spec_index(index) == a.spec_index(index + 1) == a.spec_index(index + 2)
{
    return 0;
}

}