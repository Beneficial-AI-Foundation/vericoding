//ATOM Tree
datatype Tree<T> = Leaf(T) | SingleNode(T, Tree<T>) | DoubleNode(T, Tree<T>, Tree<T>)

//ATOM Code
datatype Code<T> = CLf(T) | CSNd(T) | CDNd(T)

//ATOM serialise
function serialise<T>(t: Tree<T>): seq<Code<T>> {
  match t {
    case Leaf(v) => [CLf(v)]
    case SingleNode(v, child) => [CSNd(v)] + serialise(child)
    case DoubleNode(v, left, right) => [CDNd(v)] + serialise(right) + serialise(left)
  }
}

//ATOM deserialiseAux
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

//ATOM deserialise
function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
  requires |s| > 0
{
  deserialiseAux(s, [])
}

//ATOM testSerializeWithASingleLeaf
method testSerializeWithASingleLeaf() {
  var tree := Leaf(42);
  var codes := serialise(tree);
  assert codes == [CLf(42)];
}

//ATOM testSerializeNullValues  
method testSerializeNullValues() {
  var tree := Leaf(0);
  var codes := serialise(tree);
  assert codes == [CLf(0)];
}

//ATOM testSerializeWithAllElements
method testSerializeWithAllElements() {
  var tree := DoubleNode(1, SingleNode(2, Leaf(3)), Leaf(4));
  var codes := serialise(tree);
  assert codes == [CDNd(1), CLf(4), CSNd(2), CLf(3)];
}

//IMPL testDeseraliseWithASingleLeaf
method testDeseraliseWithASingleLeaf() {
  var codes := [CLf(42)];
  var trees := deserialise(codes);
  
  /* code modified by LLM (iteration 1): Added detailed proof steps to verify deserialization works correctly */
  // First, let's establish what deserialise(codes) computes
  assert deserialise(codes) == deserialiseAux([CLf(42)], []);
  
  // Now trace through deserialiseAux step by step
  // Step 1: deserialiseAux([CLf(42)], [])
  // codes[0] is CLf(42), so we call deserialiseAux(codes[1..], trees + [Leaf(42)])
  // which is deserialiseAux([], [] + [Leaf(42)]) = deserialiseAux([], [Leaf(42)])
  assert deserialiseAux([CLf(42)], []) == deserialiseAux([], [Leaf(42)]);
  
  // Step 2: deserialiseAux([], [Leaf(42)])  
  // Since |codes| == 0, we return trees which is [Leaf(42)]
  assert deserialiseAux([], [Leaf(42)]) == [Leaf(42)];
  
  // Therefore, the final result is [Leaf(42)]
  assert trees == [Leaf(42)];
  assert |trees| == 1;
  assert trees[0] == Leaf(42);
}

//ATOM testDeserializeWithASingleNode
method testDeserializeWithASingleNode() {
  var codes := [CSNd(1), CLf(2)];
  var trees := deserialise(codes);
  assert |trees| == 1;
  assert trees[0] == SingleNode(1, Leaf(2));
}

//ATOM testDeserialiseWithAllElements
method testDeserialiseWithAllElements() {
  var codes := [CDNd(1), CLf(4), CSNd(2), CLf(3)];
  var trees := deserialise(codes);
  assert |trees| == 1;
  assert trees[0] == DoubleNode(1, SingleNode(2, Leaf(3)), Leaf(4));
}

//ATOM SerialiseLemma
lemma SerialiseLemma<T>(t: Tree<T>)
  ensures |serialise(t)| > 0
{
}

//ATOM DeserialisetAfterSerialiseLemma
lemma DeserialisetAfterSerialiseLemma<T>(t: Tree<T>)
  ensures var s := serialise(t);
          var trees := deserialise(s);
          |trees| == 1 && trees[0] == t
{
}