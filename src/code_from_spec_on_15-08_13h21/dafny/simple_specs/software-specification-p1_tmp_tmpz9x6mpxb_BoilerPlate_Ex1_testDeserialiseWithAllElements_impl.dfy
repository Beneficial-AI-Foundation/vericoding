//ATOM
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)


//ATOM

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)


//ATOM

// Ex 1
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
 requires |codes| > 0 || |trees| > 0
 ensures |deserialiseAux(codes, trees)| >= 0
{
 if |codes| == 0 then trees
 else
  match codes[0] {
   case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)])
   case CSNd(v) => if (|trees| >= 1) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]) else trees
   case CDNd(v) => if (|trees| >= 2) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]) else trees
  }
}


//ATOM

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
 requires |s| > 0
{
 deserialiseAux(s, [])
}


//IMPL 
/* code modified by LLM (iteration 1): Fixed compilation error by removing invalid text and providing valid Dafny method implementation */
method testDeserialiseWithAllElements()
{
    // Test with a sequence that uses all three types of codes
    var codes := [CLf(1), CLf(2), CSNd(3), CDNd(4)];
    var result := deserialise(codes);
    
    // Test with just leaves
    var leafCodes := [CLf(5), CLf(6)];
    var leafResult := deserialise(leafCodes);
    
    // Test with single code
    var singleCode := [CLf(7)];
    var singleResult := deserialise(singleCode);
}