type loc = string

datatype oper = piu | mu

datatype exp =
        Boolean of bool
    |   Integer of int
    |   Op of exp * oper * exp
    |   If of exp * exp * exp
    |   Assign of loc * exp
    |   Skip 
    |   Seq of exp * exp 
    |   While of exp * exp
    |   Deref of loc 

fun valore (Integer n) = true
  | valore (Boolean b) = true
  | valore (Skip) = true
  | valore _ = false

type store = (loc * int) list



fun lookup ( [], l ) = NONE
  | lookup ( (l',n')::pairs, l) = 
    if l=l' then SOME n' else lookup (pairs,l)



fun update'  front [] (l,n) = NONE
 |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
        SOME(front @ ((l,n)::pairs) )
    else 
        update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n)


fun red (Integer n,s) = NONE
  | red (Boolean b,s) = NONE
  | red (Op (e1,opr,e2),s) = 
    (case (e1,opr,e2) of
         (Integer x1, piu, Integer x2) => SOME(Integer (x1+x2), s)   
       | (Integer x1, mu, Integer x2) => SOME(Boolean (x1 >= x2), s)
       | (e1,opr,e2) => (                                               
         if (valore e1) then (                                        
             case red (e2,s) of 
                 SOME (e2',s') => SOME (Op(e1,opr,e2'),s')     
               | NONE => NONE )                           
         else (                                                 
             case red (e1,s) of 
                 SOME (e1',s') => SOME(Op(e1',opr,e2),s')      
               | NONE => NONE ) ) )
  | red (If (e1,e2,e3),s) =
    (case e1 of
         Boolean(true) => SOME(e2,s)                           
       | Boolean(false) => SOME(e3,s)                          
       | _ => (case red (e1,s) of
                   SOME(e1',s') => SOME(If(e1',e2,e3),s')    
                 | NONE => NONE ))
  | red (Deref l,s) = 
    (case lookup  (s,l) of                
          SOME n => SOME(Integer n,s)                          
        | NONE => NONE )                  
  | red (Assign (l,e),s) =                                  
    (case e of                                                 
         Integer n => (case update (s,(l,n)) of 
                           SOME s' => SOME(Skip, s')           
                         | NONE => NONE)                                   
       | _ => (case red (e,s) of                           
                   SOME (e',s') => SOME(Assign (l,e'), s')    
                 | NONE => NONE  ) )                          
  | red (While (e1,e2),s) = SOME( If(e1,Seq(e2,While(e1,e2)),Skip),s) 
  | red (Skip,s) = NONE                                     
  | red (Seq (e1,e2),s) =                                   
    (case e1 of                                                 
        Skip => SOME(e2,s)                                     
      | _ => ( case red (e1,s) of                           
                 SOME (e1',s') => SOME(Seq (e1',e2), s')       
               | NONE => NONE ) )                                        



fun evaluate (e,s) = case red (e,s) of 
                         NONE => (e,s)
                       | SOME (e',s') => evaluate (e',s')



datatype type_L =  int  | unit  | bool

datatype type_loc = intref

type typeE = (loc*type_loc) list 


fun infertype gamma (Integer n) = SOME int
  | infertype gamma (Boolean b) = SOME bool
  | infertype gamma (Op (e1,opr,e2)) 
    = (case (infertype gamma e1, opr, infertype gamma e2) of
          (SOME int, piu, SOME int) => SOME int
        | (SOME int, mu, SOME int) => SOME bool
        | _ => NONE)
  | infertype gamma (If (e1,e2,e3)) 
    = (case (infertype gamma e1, infertype gamma e2, infertype gamma e3) of
           (SOME bool, SOME t2, SOME t3) => 
           (if t2=t3 then SOME t2 else NONE)
         | _ => NONE)
  | infertype gamma (Deref l) 
    = (case lookup (gamma,l) of
           SOME intref => SOME int
         | NONE => NONE)
  | infertype gamma (Assign (l,e)) 
    = (case (lookup (gamma,l), infertype gamma e) of
           (SOME intref,SOME int) => SOME unit
         | _ => NONE)
  | infertype gamma (Skip) = SOME unit
  | infertype gamma (Seq (e1,e2))  
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME unit, SOME t2) => SOME t2
         | _ => NONE )
  | infertype gamma (While (e1,e2)) 
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME bool, SOME unit) => SOME unit 
         | _ => NONE );


load "Listsort";
load "Int";
load "Bool";


fun printop piu = "+"
  | printop mu = ">="
                         
fun printexp (Integer n) = Int.toString n
  | printexp (Boolean b) = Bool.toString b
  | printexp (Op (e1,opr,e2)) 
    = "(" ^ (printexp e1) ^ (printop opr) 
      ^ (printexp e2) ^ ")"
  | printexp (If (e1,e2,e3)) 
    = "if " ^ (printexp e1 ) ^ " then " ^ (printexp e2)
      ^ " else " ^ (printexp e3)
  | printexp (Deref l) = "!" ^ l
  | printexp (Assign (l,e)) =  l ^ ":=" ^ (printexp e )
  | printexp (Skip) = "skip"
  | printexp (Seq (e1,e2)) =  (printexp e1 ) ^ ";" 
                                     ^ (printexp e2)
  | printexp (While (e1,e2)) =  "while " ^ (printexp e1 ) 
                                       ^ " do " ^ (printexp e2)


fun printstore' [] = ""
  | printstore' ((l,n)::pairs) = l ^ "=" ^ (Int.toString n) 
                                   ^ " " ^ (printstore' pairs)

fun printstore pairs = 
    let val pairs' = Listsort.sort 
                         (fn ((l,n),(l',n')) => String.compare (l,l'))
                         pairs
    in
        "{" ^ printstore' pairs' ^ "}" end


fun printconf (e,s) = "< " ^ (printexp e) 
                             ^ " , " ^ (printstore s) ^ " >"


fun printred' (e,s) = 
    case red (e,s) of 
        SOME (e',s') => 
        ( TextIO.print ("\n -->  " ^ printconf (e',s') ) ;
          printred' (e',s'))
      | NONE => (TextIO.print "\n -/->  " ; 
                 if valore e then 
                     TextIO.print "(a value)\n" 
                 else 
                     TextIO.print "(stuck - not a value)" )

fun printred (e,s) = (TextIO.print ("      "^(printconf (e,s))) ;
                          printred' (e,s))

