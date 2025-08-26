// Transaction logging system implementation

// <vc-spec>
method tx_write(offset: int, val: int)
  requires valid_log_state()
  requires 0 <= offset < |mem_|
  requires log_[0] < MAX_LOG_ENTRIES
  modifies this
  ensures valid_log_state()
  ensures gs == ghost_tx_write(old(gs), offset, val)
// </vc-spec>

// <vc-code>
{
    var log_idx := log_[0];
    var log_off := log_idx * 2 + 1; // +1 because log_[0] is num_entry, actual log starts at index 1;
    var old_val := mem_[offset];
    
    // Update ghost state to match what we're about to do
    gs := ghost_tx_write(gs, offset, val);
    
    // Write offset to log
    write_log(log_off, offset);
    
    // Write old value to log  
    write_log(log_off + 1, old_val);
    
    // Increment number of entries
    write_log(0, log_idx + 1);
    
    // Write new value to memory
    write_mem(offset, val);
}
// </vc-code>

// <vc-helpers>
const MAX_LOG_ENTRIES: int := 100

datatype GhostState = GhostState(entries: seq<(int, int)>, memory: seq<int>)

function ghost_tx_write(gs: GhostState, offset: int, val: int): GhostState
{
    gs.(memory := gs.memory[offset := val])
}

class TransactionLogger {
    var log_: array<int>
    var mem_: array<int>
    var gs: GhostState

    predicate valid_log_state()
        reads this, log_, mem_
    {
        log_ != null && mem_ != null &&
        log_.Length > 0 && mem_.Length > 0 &&
        0 <= log_[0] <= MAX_LOG_ENTRIES &&
        log_.Length >= log_[0] * 2 + 1
    }

    method write_log(index: int, value: int)
        requires log_ != null
        requires 0 <= index < log_.Length
        modifies log_
        ensures log_[index] == value
        ensures forall i :: 0 <= i < log_.Length && i != index ==> log_[i] == old(log_[i])
    {
        log_[index] := value;
    }

    method write_mem(index: int, value: int)
        requires mem_ != null
        requires 0 <= index < mem_.Length
        modifies mem_
        ensures mem_[index] == value
        ensures forall i :: 0 <= i < mem_.Length && i != index ==> mem_[i] == old(mem_[i])
    {
        mem_[index] := value;
    }

    method tx_write(offset: int, val: int)
      requires valid_log_state()
      requires 0 <= offset < |mem_|
      requires log_[0] < MAX_LOG_ENTRIES
      modifies this
      ensures valid_log_state()
      ensures gs == ghost_tx_write(old(gs), offset, val)
    {
        var log_idx := log_[0];
        var log_off := log_idx * 2 + 1; // +1 because log_[0] is num_entry, actual log starts at index 1;
        var old_val := mem_[offset];
        
        // Update ghost state to match what we're about to do
        gs := ghost_tx_write(gs, offset, val);
        
        // Write offset to log
        write_log(log_off, offset);
        
        // Write old value to log  
        write_log(log_off + 1, old_val);
        
        // Increment number of entries
        write_log(0, log_idx + 1);
        
        // Write new value to memory
        write_mem(offset, val);
    }
}
// </vc-helpers>