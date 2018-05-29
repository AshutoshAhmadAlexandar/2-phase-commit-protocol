-------------------------------- MODULE t2pc --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM, 
         RMMAYFAIL,
         TMMAYFAIL
(*
--algorithm TransactionCommit {
  variable rmState = [rm \in RM |-> "working"],
           tmState = "init";
  define {
    canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed", "failed"} /\ tmState # "abort"                           
    canAbort == \A rm \in RM : rmState[rm] # "committed" /\ tmState # "commit"                             
   }
  macro Prepare(p) {
    when rmState[p] = "working";
    rmState[p] := "prepared" ;    
   }
   
  macro Decide(p) {
    either { when /\ rmState[p] = "prepared"
                  /\ tmState = "commit";
             rmState[p] := "committed";
           }
    or     { when /\ rmState[p] \in {"working", "prepared"}
                  /\ tmState = "abort";
             rmState[p] := "aborted";
           }        
   }
   macro Fail(p) {
   if(RMMAYFAIL)
        {
    (*when rmState[p] \in {"working", "prepared"};*)
    rmState[p] := "failed";
        }  
   }
   
   
  fair process (RManager \in RM) {
   RS: while (rmState[self] \in {"working", "prepared"}) { 
      either Prepare(self) or Decide(self) or Fail(self)}
   }
   
   fair process (TManager = 0) {
    TS: either { await canCommit;
            TC: tmState := "commit";
                
            F1: if(TMMAYFAIL) tmState := "hidden"; 
            } 
                
            
        or { await canAbort;
             TA: tmState := "abort";
                
             F2: if(TMMAYFAIL) tmState := "hidden";
              }    
    }  
    
    fair process (BTManager = 1) {
     BS: either { await (canCommit /\ tmState = "hidden") \/ (\A rm \in RM : rmState[rm] \in {"failed",
                                                                                             "committed"});
            BC: tmState := "commit";
            }
         or { await ( canAbort /\ tmState = "hidden") \/ (\A rm \in RM : rmState[rm] \in {"failed","aborted"});
            BA: tmState := "abort";
            }
    }
}   
*)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, pc

(* define statement *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed", "failed"} /\ tmState # "abort"
canAbort == \A rm \in RM : rmState[rm] # "committed" /\ tmState # "commit"


vars == << rmState, tmState, pc >>

ProcSet == (RM) \cup {0} \cup {1}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"
                                        [] self = 1 -> "BS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                          \/ /\ \/ /\ /\ rmState[self] = "prepared"
                                      /\ tmState = "commit"
                                   /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                \/ /\ /\ rmState[self] \in {"working", "prepared"}
                                      /\ tmState = "abort"
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                          \/ /\ IF RMMAYFAIL
                                   THEN /\ rmState' = [rmState EXCEPT ![self] = "failed"]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED tmState

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

BS == /\ pc[1] = "BS"
      /\ \/ /\ (canCommit /\ tmState = "hidden") \/ (\A rm \in RM : rmState[rm] \in {"failed",
                                                                                    "committed"})
            /\ pc' = [pc EXCEPT ![1] = "BC"]
         \/ /\ ( canAbort /\ tmState = "hidden") \/ (\A rm \in RM : rmState[rm] \in {"failed","aborted"})
            /\ pc' = [pc EXCEPT ![1] = "BA"]
      /\ UNCHANGED << rmState, tmState >>

BC == /\ pc[1] = "BC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED rmState

BA == /\ pc[1] = "BA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED rmState

BTManager == BS \/ BC \/ BA

Next == TManager \/ BTManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
Consistent == \A rm1, rm2 \in RM : ~/\rmState[rm1] = "aborted" /\ rmState[rm2] = "committed"
=============================================================================
\* Modification History
\* Last modified Tue Dec 05 16:14:18 EST 2017 by ashutoshahmadalexandar
\* Created Wed Nov 29 15:16:19 EST 2017 by ashutoshahmadalexandar
