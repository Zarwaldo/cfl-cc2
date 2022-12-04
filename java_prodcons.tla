---- MODULE java_prodcons ----
EXTENDS TLC, FiniteSets, Naturals, Sequences, Integers

CONSTANTS PRODS,    (* Set of producers *)
          CONS,     (* Set of consumers *)
          CAPACITY  (* Buffer capacity *)

ASSUME /\ PRODS # {}
       /\ CONS # {}
       /\ PRODS \intersect CONS = {}
       /\ (CAPACITY > 0)

(* The goal is to write a PlusCal model of the Java producer/consumer problem 
   presented in https://www.cs.unh.edu/~charpov/programming-tlabuffer.html
 *)

(*--algorithm java_prodcons {
    variables size = 0;
    putmutex = 0;
    getmutex = 0;
    
    notified = "";
    
    waitings = {};
    
    macro SYNCHRONIZE_LOCK(mutex)   { await(mutex = 0); 
                                      mutex := 1;}
                                      
    macro SYNCHRONIZE_UNLOCK(mutex) { mutex := 0;}
    
    macro WAIT(proc) { waitings := { x \in (PRODS \cup CONS) : (x \in waitings \/ x = proc)};}
                      
    macro NOTIFY() { if(waitings # {})
                     {
                        notified := CHOOSE yy \in waitings : TRUE; waitings := { x \in waitings : x # notified};
                     }
                   }
    macro NOTIFY_ALL() { waitings := {};}
   
    (* Processes *)
        
    process (prod \in PRODS)
    {
p0:     while (TRUE) {
Penter:     SYNCHRONIZE_LOCK(putmutex);

PwaitLoop:  while(size >= CAPACITY) {
PwaitEnter:    SYNCHRONIZE_UNLOCK(putmutex);
               WAIT(self);
Pawait:        await( self \notin waitings );
PwaitExit:     SYNCHRONIZE_LOCK(putmutex);
            };
Pnotify:    NOTIFY();
            
Pwrite:      size := size + 1;     
            
Pexit:      SYNCHRONIZE_UNLOCK(putmutex);
       }
    }

    process (cons \in CONS)
    {
c0:     while (TRUE) {
Center:     SYNCHRONIZE_LOCK(getmutex);

CwaitLoop:  while(size <= 0) {
CwaitEnter:    SYNCHRONIZE_UNLOCK(getmutex);
               WAIT(self);
Cawait:        await( self \notin waitings );
CwaitExit:     SYNCHRONIZE_LOCK(getmutex);
            };
Cnotify:    NOTIFY();
            
Cread:      size := size - 1;     
            
Cexit:      SYNCHRONIZE_UNLOCK(getmutex);
       }
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "9ac56398" /\ chksum(tla) = "82520508")
VARIABLES size, putmutex, getmutex, notified, waitings, pc

vars == << size, putmutex, getmutex, notified, waitings, pc >>

ProcSet == (PRODS) \cup (CONS)

Init == (* Global variables *)
        /\ size = 0
        /\ putmutex = 0
        /\ getmutex = 0
        /\ notified = ""
        /\ waitings = {}
        /\ pc = [self \in ProcSet |-> CASE self \in PRODS -> "p0"
                                        [] self \in CONS -> "c0"]

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "Penter"]
            /\ UNCHANGED << size, putmutex, getmutex, notified, waitings >>

Penter(self) == /\ pc[self] = "Penter"
                /\ (putmutex = 0)
                /\ putmutex' = 1
                /\ pc' = [pc EXCEPT ![self] = "PwaitLoop"]
                /\ UNCHANGED << size, getmutex, notified, waitings >>

PwaitLoop(self) == /\ pc[self] = "PwaitLoop"
                   /\ IF size >= CAPACITY
                         THEN /\ pc' = [pc EXCEPT ![self] = "PwaitEnter"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Pnotify"]
                   /\ UNCHANGED << size, putmutex, getmutex, notified, 
                                   waitings >>

PwaitEnter(self) == /\ pc[self] = "PwaitEnter"
                    /\ putmutex' = 0
                    /\ waitings' = { x \in (PRODS \cup CONS) : (x \in waitings \/ x = self)}
                    /\ pc' = [pc EXCEPT ![self] = "Pawait"]
                    /\ UNCHANGED << size, getmutex, notified >>

Pawait(self) == /\ pc[self] = "Pawait"
                /\ ( self \notin waitings )
                /\ pc' = [pc EXCEPT ![self] = "PwaitExit"]
                /\ UNCHANGED << size, putmutex, getmutex, notified, waitings >>

PwaitExit(self) == /\ pc[self] = "PwaitExit"
                   /\ (putmutex = 0)
                   /\ putmutex' = 1
                   /\ pc' = [pc EXCEPT ![self] = "PwaitLoop"]
                   /\ UNCHANGED << size, getmutex, notified, waitings >>

Pnotify(self) == /\ pc[self] = "Pnotify"
                 /\ IF waitings # {}
                       THEN /\ notified' = (CHOOSE yy \in waitings : TRUE)
                            /\ waitings' = { x \in waitings : x # notified'}
                       ELSE /\ TRUE
                            /\ UNCHANGED << notified, waitings >>
                 /\ pc' = [pc EXCEPT ![self] = "Pwrite"]
                 /\ UNCHANGED << size, putmutex, getmutex >>

Pwrite(self) == /\ pc[self] = "Pwrite"
                /\ size' = size + 1
                /\ pc' = [pc EXCEPT ![self] = "Pexit"]
                /\ UNCHANGED << putmutex, getmutex, notified, waitings >>

Pexit(self) == /\ pc[self] = "Pexit"
               /\ putmutex' = 0
               /\ pc' = [pc EXCEPT ![self] = "p0"]
               /\ UNCHANGED << size, getmutex, notified, waitings >>

prod(self) == p0(self) \/ Penter(self) \/ PwaitLoop(self)
                 \/ PwaitEnter(self) \/ Pawait(self) \/ PwaitExit(self)
                 \/ Pnotify(self) \/ Pwrite(self) \/ Pexit(self)

c0(self) == /\ pc[self] = "c0"
            /\ pc' = [pc EXCEPT ![self] = "Center"]
            /\ UNCHANGED << size, putmutex, getmutex, notified, waitings >>

Center(self) == /\ pc[self] = "Center"
                /\ (getmutex = 0)
                /\ getmutex' = 1
                /\ pc' = [pc EXCEPT ![self] = "CwaitLoop"]
                /\ UNCHANGED << size, putmutex, notified, waitings >>

CwaitLoop(self) == /\ pc[self] = "CwaitLoop"
                   /\ IF size <= 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "CwaitEnter"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Cnotify"]
                   /\ UNCHANGED << size, putmutex, getmutex, notified, 
                                   waitings >>

CwaitEnter(self) == /\ pc[self] = "CwaitEnter"
                    /\ getmutex' = 0
                    /\ waitings' = { x \in (PRODS \cup CONS) : (x \in waitings \/ x = self)}
                    /\ pc' = [pc EXCEPT ![self] = "Cawait"]
                    /\ UNCHANGED << size, putmutex, notified >>

Cawait(self) == /\ pc[self] = "Cawait"
                /\ ( self \notin waitings )
                /\ pc' = [pc EXCEPT ![self] = "CwaitExit"]
                /\ UNCHANGED << size, putmutex, getmutex, notified, waitings >>

CwaitExit(self) == /\ pc[self] = "CwaitExit"
                   /\ (getmutex = 0)
                   /\ getmutex' = 1
                   /\ pc' = [pc EXCEPT ![self] = "CwaitLoop"]
                   /\ UNCHANGED << size, putmutex, notified, waitings >>

Cnotify(self) == /\ pc[self] = "Cnotify"
                 /\ IF waitings # {}
                       THEN /\ notified' = (CHOOSE yy \in waitings : TRUE)
                            /\ waitings' = { x \in waitings : x # notified'}
                       ELSE /\ TRUE
                            /\ UNCHANGED << notified, waitings >>
                 /\ pc' = [pc EXCEPT ![self] = "Cread"]
                 /\ UNCHANGED << size, putmutex, getmutex >>

Cread(self) == /\ pc[self] = "Cread"
               /\ size' = size - 1
               /\ pc' = [pc EXCEPT ![self] = "Cexit"]
               /\ UNCHANGED << putmutex, getmutex, notified, waitings >>

Cexit(self) == /\ pc[self] = "Cexit"
               /\ getmutex' = 0
               /\ pc' = [pc EXCEPT ![self] = "c0"]
               /\ UNCHANGED << size, putmutex, notified, waitings >>

cons(self) == c0(self) \/ Center(self) \/ CwaitLoop(self)
                 \/ CwaitEnter(self) \/ Cawait(self) \/ CwaitExit(self)
                 \/ Cnotify(self) \/ Cread(self) \/ Cexit(self)

Next == (\E self \in PRODS: prod(self))
           \/ (\E self \in CONS: cons(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


GoodBuffer == [](size>=0 /\ size<=CAPACITY)

DeadLock == [](~(waitings =  {"p1", "p2", "p3", "c1", "c2"}))


====
