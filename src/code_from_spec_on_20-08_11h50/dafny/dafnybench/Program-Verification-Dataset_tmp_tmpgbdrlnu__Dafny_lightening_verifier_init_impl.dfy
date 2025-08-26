method Main() {
  // Variables need to be properly declared and the conditional needs to be complete
  var f: bool := true;
  var off: int := 0;
  var first_log_pos: set<int> := {};
  var s := if f && !(off in first_log_pos) then true else false;
}