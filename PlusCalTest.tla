---------------------------- MODULE PlusCalTest ----------------------------

EXTENDS Integers

(* --fair algorithm mutexes
variables lock = 0, notified = FALSE, ready = FALSE, processed = FALSE;

macro mutex_lock() begin await lock = 0; lock := 1; end macro

macro mutex_unlock() begin lock := 0; end macro

macro mutex_raii() begin await lock = 0; end macro

macro cv_wait_lock(condition)
begin
    await condition /\ notified;
    notified := FALSE;
    mutex_lock();
end macro

macro cv_wait_raii(condition)
begin
    await condition /\ notified;
    notified := FALSE;
    mutex_raii();
end macro

macro cv_notify() begin notified := TRUE; end macro


process Worker = 1
begin
w_ncs:
    skip;
w_acquire:
    cv_wait_lock(ready);
w_cs:
    processed := TRUE;
w_release:
    mutex_unlock();
w_notify:
    cv_notify();
end process;

process Main = 2
begin
m_ncs:
    skip;
m_acquire:
    mutex_lock();
m_cs:
    ready := TRUE;
m_release:
    mutex_unlock();
m_notify:
    cv_notify();
m_wait:
    cv_wait_raii(processed)
end process;

end algorithm *)


\* BEGIN TRANSLATION
VARIABLES lock, notified, ready, processed, pc

vars == << lock, notified, ready, processed, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ lock = 0
        /\ notified = FALSE
        /\ ready = FALSE
        /\ processed = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "w_ncs"
                                        [] self = 2 -> "m_ncs"]

w_ncs == /\ pc[1] = "w_ncs"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![1] = "w_acquire"]
         /\ UNCHANGED << lock, notified, ready, processed >>

w_acquire == /\ pc[1] = "w_acquire"
             /\ ready /\ notified
             /\ notified' = FALSE
             /\ lock = 0
             /\ lock' = 1
             /\ pc' = [pc EXCEPT ![1] = "w_cs"]
             /\ UNCHANGED << ready, processed >>

w_cs == /\ pc[1] = "w_cs"
        /\ processed' = TRUE
        /\ pc' = [pc EXCEPT ![1] = "w_release"]
        /\ UNCHANGED << lock, notified, ready >>

w_release == /\ pc[1] = "w_release"
             /\ lock' = 0
             /\ pc' = [pc EXCEPT ![1] = "w_notify"]
             /\ UNCHANGED << notified, ready, processed >>

w_notify == /\ pc[1] = "w_notify"
            /\ notified' = TRUE
            /\ pc' = [pc EXCEPT ![1] = "Done"]
            /\ UNCHANGED << lock, ready, processed >>

Worker == w_ncs \/ w_acquire \/ w_cs \/ w_release \/ w_notify

m_ncs == /\ pc[2] = "m_ncs"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![2] = "m_acquire"]
         /\ UNCHANGED << lock, notified, ready, processed >>

m_acquire == /\ pc[2] = "m_acquire"
             /\ lock = 0
             /\ lock' = 1
             /\ pc' = [pc EXCEPT ![2] = "m_cs"]
             /\ UNCHANGED << notified, ready, processed >>

m_cs == /\ pc[2] = "m_cs"
        /\ ready' = TRUE
        /\ pc' = [pc EXCEPT ![2] = "m_release"]
        /\ UNCHANGED << lock, notified, processed >>

m_release == /\ pc[2] = "m_release"
             /\ lock' = 0
             /\ pc' = [pc EXCEPT ![2] = "m_notify"]
             /\ UNCHANGED << notified, ready, processed >>

m_notify == /\ pc[2] = "m_notify"
            /\ notified' = TRUE
            /\ pc' = [pc EXCEPT ![2] = "m_wait"]
            /\ UNCHANGED << lock, ready, processed >>

m_wait == /\ pc[2] = "m_wait"
          /\ processed /\ notified
          /\ notified' = FALSE
          /\ lock = 0
          /\ pc' = [pc EXCEPT ![2] = "Done"]
          /\ UNCHANGED << lock, ready, processed >>

Main == m_ncs \/ m_acquire \/ m_cs \/ m_release \/ m_notify \/ m_wait

Next == Worker \/ Main
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


Safety == /\ (\A i \in ProcSet, j \in ProcSet : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs"))
          /\ processed => ready
          /\ notified => (lock # 1)  
          
Processed == /\Termination 
             /\ <>[]processed
             /\ (ready ~> processed)

=============================================================================
\* Modification History
\* Last modified Sun Jul 29 16:34:09 CEST 2018 by pascal
\* Created Sat Jul 28 12:31:06 CEST 2018 by pascal
