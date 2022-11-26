---- MODULE java_prodcons ----
EXTENDS TLC, FiniteSets, Naturals

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

    (* Processes *)
        
    process (prod \in PRODS)
    {
       (* put *)
p0:    while (TRUE) {
         skip;
       }
    }

    process (cons \in CONS)
    {
      (* get *)
c0:   while (TRUE) {
        skip;
      }
    }
} *)
====
