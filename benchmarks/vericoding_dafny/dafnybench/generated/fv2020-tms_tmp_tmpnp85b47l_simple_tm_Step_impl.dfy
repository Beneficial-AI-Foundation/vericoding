module ModelingTM {
    type ProcessId = nat
    type MemoryObject = nat
    type TimeStamp = nat

    class Operation {
        const isWrite: bool
        const memObject: MemoryObject
    }

    class Transaction {
        const ops: seq<Operation>
    }

    // Process state : transaction progress and process memory.
    class ProcessState {
        // currentTx : id of tx being processed. txs.size() means done.
        const currentTx: nat
        // currentOp :
        //      - tx.ops.size() represents tryCommit operation.
        //      - -1 represents abort operation
        //      - values in between represent read and write operations
        const currentOp: int
        // sub-operations of the operation, see the step function
        const currentSubOp: nat

        // Set of read objects with original observed timestamp.
        const readSet: map<MemoryObject, TimeStamp>
        // Set of written objects.
        const writeSet: set<MemoryObject>

// <vc-spec>
        constructor () {
            currentTx := 0;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor nextSubOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp + 1
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp + 1;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor nextOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp + 1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp + 1;
            currentSubOp := 0;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor abortTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == -1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := -1;
            currentSubOp := 0;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor restartTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {
            currentTx := that.currentTx;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor nextTx(that: ProcessState)
            ensures this.currentTx == that.currentTx + 1
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {
            currentTx := that.currentTx + 1;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor addToReadSet(that: ProcessState, obj: MemoryObject, ts: TimeStamp)
            ensures currentTx == that.currentTx
            ensures currentOp == that.currentOp
            ensures currentSubOp == that.currentSubOp
            ensures readSet.Keys == that.readSet.Keys + {obj}
                && readSet[obj] == ts
                && forall o :: o in readSet && o != obj ==> readSet[o] == that.readSet[o]
            ensures writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp;
            readSet := that.readSet[obj := ts];
            writeSet := that.writeSet;
        }

        constructor addToWriteSet(that: ProcessState, obj: MemoryObject)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet + {obj}
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp;
            readSet := that.readSet;
            writeSet := that.writeSet + {obj};
        }
    }

    class TMSystem {
        // Ordered list of transaction that each process should process
        const txQueues : map<ProcessId, seq<Transaction>>
        // State and memory of processes
        const procStates : map<ProcessId, ProcessState>
        // Dirty objects. (Replaces the object value in a real representation. Used for safety proof)
        const dirtyObjs: set<MemoryObject>
        // Object lock.
        const lockedObjs: set<MemoryObject>
        // Object timestamp. (Incremented at the end of any write transaction)
        const objTimeStamps: map<MemoryObject, nat>

        constructor (q: map<ProcessId, seq<Transaction>>) {
            txQueues := q;
            procStates := map[];
            dirtyObjs := {};
            lockedObjs := {};
            objTimeStamps := map[];
        }

        constructor initTimestamp(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys ==  that.objTimeStamps.Keys + {obj}
                && objTimeStamps[obj] == 0
                && forall o :: o in objTimeStamps && o != obj ==> objTimeStamps[o] == that.objTimeStamps[o]
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps[obj := 0];
        }

        constructor updateState(that: TMSystem, pid: ProcessId, state: ProcessState)
            ensures txQueues == that.txQueues
            ensures procStates.Keys == that.procStates.Keys + {pid}
                && procStates[pid] == state
                && forall p :: p in procStates && p != pid ==> procStates[p] == that.procStates[p]
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates[pid := state];
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }

        constructor markDirty(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs + {obj}
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs + {obj};
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }

        constructor clearDirty(that: TMSystem, writeSet: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs - writeSet
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs - writeSet;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }

        constructor acquireLock(that: TMSystem, o: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs + {o}
            ensures objTimeStamps == that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs + {o};
            objTimeStamps := that.objTimeStamps;
        }

        constructor releaseLocks(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs - objs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs - objs;
            objTimeStamps := that.objTimeStamps;
        }

        constructor updateTimestamps(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys == that.objTimeStamps.Keys
                && forall o :: o in that.objTimeStamps ==>
                if(o in objs) then objTimeStamps[o] != that.objTimeStamps[o] else objTimeStamps[o] == that.objTimeStamps[o]
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := map o | o in that.objTimeStamps ::
                if(o in objs) then (that.objTimeStamps[o] + 1) else that.objTimeStamps[o];
        }

        predicate stateValid(pid: ProcessId, state: ProcessState)
            requires pid in procStates && state == procStates[pid]
        {
            && pid in txQueues
            && state.currentTx <= |txQueues[pid]|
            && if state.currentTx == |txQueues[pid]| then (
                // Queue finished
                && state.currentOp == 0
                && state.currentSubOp == 0
                && |state.readSet| == 0
                && |state.writeSet| == 0
            ) else if state.currentTx < |txQueues[pid]| then (
                // Queue unfinished
                && exists tx :: (
                    && tx == txQueues[pid][state.currentTx]
                    && state.currentOp <= |tx.ops|
                    && state.currentOp >= -1
                    && if (state.currentOp >= 0 && state.currentOp < |tx.ops|) then (
                        // Read/Write operations have at most two subOps
                        state.currentSubOp < 2
                    ) else if state.currentOp == |tx.ops| then (
                        // tryCommit has 4 subOps
                        state.currentSubOp < 4
                    ) else if state.currentOp == -1 then (
                        // abort has 3 subOps
                        state.currentSubOp < 3
                    ) else false
                )
                && state.readSet.Keys <= objTimeStamps.Keys
                && state.writeSet <= lockedObjs
            ) else false
        }

        predicate validSystem()
        {
            && procStates.Keys <= txQueues.Keys
            && dirtyObjs <= objTimeStamps.Keys
            && lockedObjs <= objTimeStamps.Keys
            && forall p, s :: p in procStates && s == procStates[p] ==> stateValid(p, s)
        }
    }

// <vc-helpers>
// </vc-helpers>

method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
        requires pid in input.txQueues
        requires pid in input.procStates
        requires input.validSystem()
        ensures system.validSystem()
// </vc-spec>
// <vc-code>
{
  var state := input.procStates[pid];
  
  if state.currentTx >= |input.txQueues[pid]| {
    // Transaction queue is finished, no step to take
    system := input;
    return;
  }
  
  var tx := input.txQueues[pid][state.currentTx];
  
  if state.currentOp == -1 {
    // Abort operation
    if state.currentSubOp == 0 {
      // Release locks
      var newState := new ProcessState.nextSubOp(state);
      system := new TMSystem.releaseLocks(input, state.writeSet);
      system := new TMSystem.updateState(system, pid, newState);
    } else if state.currentSubOp == 1 {
      // Clear write set and read set, restart transaction
      var newState := new ProcessState.restartTx(state);
      system := new TMSystem.updateState(input, pid, newState);
    } else {
      // Should not happen based on stateValid
      system := input;
    }
  } else if state.currentOp >= 0 && state.currentOp < |tx.ops| {
    // Regular read/write operation
    var op := tx.ops[state.currentOp];
    var obj := op.memObject;
    
    // Initialize timestamp if needed
    if obj !in input.objTimeStamps {
      system := new TMSystem.initTimestamp(input, obj);
    } else {
      system := input;
    }
    
    if op.isWrite {
      // Write operation
      if state.currentSubOp == 0 {
        // Try to acquire lock
        if obj in system.lockedObjs {
          // Lock conflict, abort
          var newState := new ProcessState.abortTx(state);
          system := new TMSystem.updateState(system, pid, newState);
        } else {
          // Acquire lock and proceed
          system := new TMSystem.acquireLock(system, obj);
          var newState := new ProcessState.nextSubOp(state);
          system := new TMSystem.updateState(system, pid, newState);
        }
      } else {
        // Add to write set, mark dirty, move to next operation
        system := new TMSystem.markDirty(system, obj);
        var newState := new ProcessState.addToWriteSet(state, obj);
        newState := new ProcessState.nextOp(newState);
        system := new TMSystem.updateState(system, pid, newState);
      }
    } else {
      // Read operation
      if state.currentSubOp == 0 {
        // Check if object is dirty
        if obj in system.dirtyObjs {
          // Dirty read, abort
          var newState := new ProcessState.abortTx(state);
          system := new TMSystem.updateState(system, pid, newState);
        } else {
          // Clean read, proceed
          var newState := new ProcessState.nextSubOp(state);
          system := new TMSystem.updateState(system, pid, newState);
        }
      } else {
        // Add to read set with current timestamp, move to next operation
        var ts := system.objTimeStamps[obj];
        var newState := new ProcessState.addToReadSet(state, obj, ts);
        newState := new ProcessState.nextOp(newState);
        system := new TMSystem.updateState(system, pid, newState);
      }
    }
  } else if state.currentOp == |tx.ops| {
    // Commit operation
    if state.currentSubOp == 0 {
      // Validate read set
      var valid := forall obj :: obj in state.readSet ==>;
        obj in system.objTimeStamps && state.readSet[obj] == system.objTimeStamps[obj];
      
      if !valid {
        // Validation failed, abort
        var newState := new ProcessState.abortTx(state);
        system := new TMSystem.updateState(system, pid, newState);
      } else {
        // Validation passed, proceed
        var newState := new ProcessState.nextSubOp(state);
        system := new TMSystem.updateState(system, pid, newState);
      }
    } else if state.currentSubOp == 1 {
      // Update timestamps for written objects
      system := new TMSystem.updateTimestamps(system, state.writeSet);
      var newState := new ProcessState.nextSubOp(state);
      system := new TMSystem.updateState(system, pid, newState);
    } else if state.currentSubOp == 2 {
      // Clear dirty objects and release locks
      system := new TMSystem.clearDirty(system, state.writeSet);
      system := new TMSystem.releaseLocks(system, state.writeSet);
      var newState := new ProcessState.nextSubOp(state);
      system := new TMSystem.updateState(system, pid, newState);
    } else {
      // Move to next transaction
      var newState := new ProcessState.nextTx(state);
      system := new TMSystem.updateState(system, pid, newState);
    }
  } else {
    // Should not happen
    system := input;
  }
}
// </vc-code>

}