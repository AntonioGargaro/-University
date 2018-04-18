(*Antonio Gargaro H00218711 Foundations 1 Assignment SML*)


(*note that in the program below, the list of reduction steps given by
mreduce has many duplications.  This is very easy to avoid by
monitoring l2,l3,l4, l5,l6, etc, in mreduce and the print functions.
This is your job to do. *)

(*Datatypes*)
datatype LEXP = APP of LEXP * LEXP | LAM of string * LEXP | ID of string
datatype BEXP = BAPP of BEXP * BEXP | BLAM of BEXP | BID of int;
datatype IEXP = IAPP of IEXP * IEXP | ILAM of string * IEXP | IID of string;
datatype IBEXP = IBAPP of IBEXP * IBEXP | IBLAM of IBEXP | IBID of int;
datatype COM = CAPP of COM*COM | CID of string | CI | CK | CS;

(* checks whether a variable is free in a term *)

fun free id1 (ID id2) = if (id1 = id2) then  true else false|
    free id1 (APP(e1,e2))= (free id1 e1) orelse (free id1 e2) | 
    free id1 (LAM(id2, e1)) = if (id1 = id2) then false else (free id1 e1);

(* finds new variables which are fresh  in l and different from id*)
    
fun findme id l = (let val id1 = id^"1"  in if not (List.exists (fn x => id1 = x) l) then id1 else (findme id1 l) end);


(* finds the list of free variables in a term *)

fun freeVars (ID id2)       = [id2]
  | freeVars (APP(e1,e2))   = freeVars e1 @ freeVars e2
  | freeVars (LAM(id2, e1)) = List.filter (fn x => not (x = id2)) (freeVars e1);


(*does substitution avoiding the capture of free variables*)

fun subs e id (ID id1) =  if id = id1 then e else (ID id1) |
    subs e id (APP(e1,e2)) = APP(subs e id e1, subs e id e2)|
    subs e id (LAM(id1,e1)) = (if id = id1 then LAM(id1,e1) else
                                   if (not (free id e1) orelse not (free id1 e))
				       then LAM(id1,subs e id e1)
                                   else (let val id2 = (findme id ([id1]@ (freeVars e) @ (freeVars e1)))
					 in LAM(id2, subs e id (subs (ID id2) id1 e1)) end));





(*Prints a term*)
fun printLEXP (ID v) =
    print v
  | printLEXP (LAM (v,e)) =
    (print "(\\";
     print v;
     print ".";
     printLEXP e;
     print ")")
  | printLEXP (APP(e1,e2)) =
    (print "(";
     printLEXP e1;
     print " ";
     printLEXP e2;
     print ")");

(*Finds a beta redex*)
fun is_redex (APP(LAM(_,_),_)) =
      true
  | is_redex _ =
      false;

fun is_var (ID id) =  true |
    is_var _ = false;


(*the function below adds lambda id to a list of terms *)
fun addlam id [] = [] |
    addlam id (e::l) = (LAM(id,e))::(addlam id l);

(*similar to above but adds app backward *)
fun addbackapp [] e2 = []|
    addbackapp (e1::l) e2 = (APP(e1,e2)):: (addbackapp l e2);

(*similar to above but adds app forward *)
fun addfrontapp e1 [] = []|
    addfrontapp e1  (e2::l) = (APP(e1,e2)):: (addfrontapp e1 l);

(*Prints steps taken in reduce*)
fun printSteps 0 = print ""
|	printSteps n = (print "\n"; print (Int.toString n); print " steps");

(*prints elements from a list putting an arrow in between*)
fun printlistreduce [] 0 = ()|
    printlistreduce (e::[]) n = (printLEXP e; printSteps n) |
    printlistreduce (e::m::l) n = (if e = m then printlistreduce (m::l) n else
								(printLEXP e; print" -->\n"; printlistreduce (m::l) (n+1)));

fun debuglist n l = (print n; print ": "; printlistreduce l 0; print "\n");

(*beta-reduces a redex*)

fun red (APP(LAM(id,e1),e2)) = subs e2 id e1;

(*reduces a term to normal form using the m-strategy in which the contracted redex is:
 m(AB) = m(A) if m(A) is defined
 m(AB) = m(B) if m(A) undefined and m(B) defined
 m(AB) = AB if m(A) undefined and m(B) undefined and AB redex
 m(AB) = undefined
 m(\v.A) = m(A)
 m(v) = undefined *)



fun mreduce (ID id) =  [(ID id)] | 
    mreduce (LAM(id,e)) = (addlam id (mreduce e)) |
    mreduce (APP(e1,e2)) = (let val l1 = (mreduce e1)
				val l2 = (mreduce e2)
				val l3 = (addbackapp l1 e2)				
				val l4 = (addfrontapp (List.last l1) l2)
				val l5 = (List.last l4)
				val l6 =  if (is_redex l5) then (mreduce (red l5)) else [l5]
			    in l3 @ l4 @ l6
			    end);


(*printmreduce first m-reduces the term giving the list of all intermediary 
terms and then prints this list separating intermediary terms with -->*)

fun printmreduce e = (let val tmp =  (mreduce e)
		      in printlistreduce tmp 0 end);



fun has_redex (ID id) = false |
    has_redex (LAM(id,e)) = has_redex e|
    has_redex (APP(e1,e2)) = if (is_redex  (APP(e1,e2))) then true else
                              ((has_redex e1) orelse (has_redex e2));

fun  one_rireduce (ID id) = (ID id)|
    one_rireduce (LAM(id,e)) = LAM(id, (one_rireduce e))|
    one_rireduce (APP(e1,e2)) = if (has_redex e2) then (APP(e1, (one_rireduce e2))) else
                                if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                          if (has_redex e1) then (APP((one_rireduce e1), e2)) else
                                              (APP(e1,e2));



fun rireduce (ID id) =  [(ID id)] |
    rireduce (LAM(id,e)) = (addlam id (rireduce e)) |
    rireduce (APP(e1,e2)) = (let val l1 = (rireduce e2)
				val e3 = (List.last l1)
                                val l2 = (addfrontapp e1 l1)
				val e4 = (APP(e1,e3))
                                val l3 =  if (is_redex e4) then (rireduce (red e4)) else 
					  if is_var(e1) then [e4] else
					      (rireduce (APP(one_rireduce e1, e3)))
			    in l2 @ l3
                            end);


fun printrireduce e = (let val tmp =  (rireduce e)
		      in printlistreduce tmp 0 end);

fun one_loreduce (ID id) = (ID id)|
    one_loreduce (LAM(id,e)) = LAM(id, (one_loreduce e))|
    one_loreduce (APP(e1,e2)) = if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                 if (has_redex e1) then APP(one_loreduce e1, e2) else
                                 if (has_redex e2) then APP(e1, (one_loreduce e2)) else (APP(e1,e2));


fun loreduce (ID id) =  [(ID id)] |
    loreduce (LAM(id,e)) = (addlam id (loreduce e)) |
    loreduce (APP(e1,e2)) = (let val l1 = if (is_redex (APP(e1,e2))) then  (loreduce (red (APP(e1,e2)))) else 
				 if (has_redex e1) then (loreduce (APP(one_loreduce e1, e2))) else 
				 if (has_redex e2) then  (loreduce (APP(e1, (one_loreduce e2)))) else []
				 in [APP(e1,e2)]@l1
			      end);


fun printloreduce e = (let val tmp =  (loreduce e)
		      in printlistreduce tmp 0 end);

findme   "x" ["x", "x1", "x11", "x111"];


val vx = (ID "x");
val vy = (ID "y");
val vz = (ID "z");
val t1 = (LAM("x",vx));
val t2 = (LAM("y",vx));
val t3 = (APP(APP(t1,t2),vz));
val t4 = (APP(t1,vz));
val t5 = (APP(t3,t3));
val t6 = (LAM("x",(LAM("y",(LAM("z",(APP(APP(vx,vz),(APP(vy,vz))))))))));
val t7 = (APP(APP(t6,t1),t1));
val t8 = (LAM("z", (APP(vz,(APP(t1,vz))))));
val t9 = (APP(t8,t3));

(*My SML Code for the assignment starts here!*)

(*Question 3
  For each of the val term names I put the letter 
  for the corresponding datatype infront of it.
  E.g LEXP's val name "val t1" = BEXP's val name "Bt1".*)
(*BEXP*)
val Bvx = (BID 1);
val Bvy = (BID 2);
val Bvz = (BID 3);
val Bt1 = (BLAM(Bvx));
val Bt2 = (BLAM(Bvx));
val Bt3 = (BAPP(BAPP(Bt1,Bt2),Bvz));
val Bt4 = (BAPP(Bt1,Bvz));
val Bt5 = (BAPP(Bt3,Bt3));
val Bt6 = (BLAM((BLAM((BLAM((BAPP(BAPP(Bvx,Bvz),(BAPP(Bvy,Bvz))))))))));
val Bt7 = (BAPP(BAPP(Bt6,Bt1),Bt1));
val Bt8 = (BLAM(BAPP(Bvz,(BAPP(Bt1,Bvz)))));
val Bt9 = (BAPP(Bt8,Bt3));

(*IEXP*)
val Ivx = (IID "x");
val Ivy = (IID "y");
val Ivz = (IID "z");
val It1 = (ILAM("x", Ivx));
val It2 = (ILAM("y", Ivx));
val It3 = (IAPP(Ivz, IAPP(It2, It1)));
val It4 = (IAPP(Ivz, It1));
val It5 = (IAPP(It3, It3));
val It6 = (ILAM("x", (ILAM("y", (ILAM("z", (IAPP(IAPP(Ivz, Ivy), IAPP(Ivz, Ivx)))))))));
val It7 = (IAPP(It1, (IAPP(It1, It6))));
val It8 = (ILAM("z", (IAPP(IAPP(Ivz, It1), Ivz))));
val It9 = (IAPP(It3, It8));

(*IBEXP*)
val IBvx = (IBID 1);
val IBvy = (IBID 2);
val IBvz = (IBID 3);
val IBt1 = (IBLAM(IBvx));
val IBt2 = (IBLAM(IBvx));
val IBt3 = (IBAPP(IBvz, IBAPP(IBt2, IBt1)));
val IBt4 = (IBAPP(IBvz, IBt1));
val IBt5 = (IBAPP(IBt3, IBt3));
val IBt6 = (IBLAM(IBLAM(IBLAM(IBAPP(IBAPP(IBvz, IBvy), IBAPP(IBvz, IBvx))))));
val IBt7 = (IBAPP(IBt1, (IBAPP(IBt1, IBt6))));
val IBt8 = (IBLAM(IBAPP(IBAPP(IBvz, IBt1), IBvz)));
val IBt9 = (IBAPP(IBt3, IBt8));

(*COM*)
val Cvx = (CID "x");
val Cvy = (CID "y");
val Cvz = (CID "z");
val Ct1 = (CI);
val Ct2 = (CAPP(CK, Cvx));
val Ct3 = (CAPP(CAPP(Ct1, Ct2), Cvz));
val Ct4 = (CAPP(Ct1, Cvz));
val Ct5 = (CAPP(Ct3, Ct3));
val Ct6 = (CAPP(CAPP(CAPP(CAPP(CK, CK), CS), Cvx), Cvy));
val Ct7 = (CAPP(CAPP(Ct6, Ct1), Ct1));
val Ct8 = (CAPP(CAPP(CS, CI), CI));
val Ct9 = (CAPP(Ct8, Ct3));




(*Question 4 Printing Functions*)

(*Prints a term in classical λ-calculus with de Bruijn indices*)
fun printBEXP (BID v) = 
	print (Int.toString v)
|	printBEXP (BLAM (e)) =
	(print "(\\";
	printBEXP e;
	print ")")
| printBEXP (BAPP (e1, e2)) =
	(print "(";
	printBEXP e1;
	print " ";
	printBEXP e2;
	print ")");
	
(*Prints a term in λ-calculus in item notation*)
fun printIEXP (IID v) =
	print v 
| printIEXP (ILAM (v,e)) = 
	(print "["; 
	print v; 
	print "]"; 
	printIEXP e)
| printIEXP (IAPP(e1,e2)) =
	(print "<"; 
	printIEXP e1; 
	print ">"; 
	printIEXP e2);

(*Prints a term in λ-calculus in item notation with de Bruijn indices*)
fun printIBEXP (IBID v) = 
	print (Int.toString(v)) 
| printIBEXP (IBLAM(e)) = 
	(print "["; 
	print "]"; 
	printIBEXP e)
| printIBEXP (IBAPP(e1,e2)) =
	(print "<";
	printIBEXP e1; 
	print ">"; 
	printIBEXP e2);
	
(*Prints a term in combinatory logic*)
fun printCOM (CID v) = 
	print v 
| printCOM(CI) = 
	print "I''"
| printCOM(CK) = 
	print "K''"
| printCOM(CS) = 
	print "S''"
| printCOM(CAPP (e1,e2)) =
	(print "(";
	printCOM e1;
	print " ";
	printCOM e2;
	print ")");


	
	
	

(*Question 5*)


fun cfree id1 (CID id2) = 
	if (id1 = id2) then true else false 
| cfree id1 (CAPP(e1,e2)) = 
	(cfree id1 e1) orelse (cfree id1 e2) 
| cfree id1 (CI) = 
	false
| cfree id1 (CK) = 
	false
| cfree id1 (CS) =
	false;
   
   
(*Combinator functions*)
fun cfunf id (CID id1) =
            if id = id1 then CI
              else CAPP(CK,(CID id1)) |
                cfunf id(CAPP(e1,e2))=
            if not(cfree id (CAPP(e1,e2)))
               then CAPP(CK,CAPP(e1,e2))
              else
                if((CID id) = e2) andalso not(cfree id e1)
                  then e1
                  else CAPP(CAPP(CS,(cfunf id e1)),(cfunf id e2));
				  
        
(*U: M to M'' Translation - LEXP to COM*)
fun toC (ID id) = 
    (CID id)
| toC (LAM(id, e)) = 
    cfunf id (toC e)
| toC (APP(e1,e2)) = 
    CAPP(toC e1, toC e2);   
    
    
(*T: M' to M'' Translation - IEXP to COM*)
fun itoC (IID v) =
    (CID v)
| itoC (ILAM(v,e)) = 
    cfunf v (itoC e)
| itoC (IAPP(e2,e1)) =
    CAPP(itoC e1, itoC e2);
	
(*V: M to M' Translation - LEXP to IEXP*)	
fun ltoI (ID v) =
	(IID v)
| ltoI (APP(e1,e2)) =
	(IAPP(ltoI e2, ltoI e1))
| ltoI (LAM(v, e)) =
	(ILAM(v, ltoI e));


(*Question 7*)
fun subterm2 (CID id) =
	[CID id]
| subterm2 (CI) =
	[CI]
| subterm2 (CK) =
	[CK]
| subterm2 (CS) =
	[CS]
| subterm2 (CAPP(e1,e2)) =
	[CAPP(e1, e2)] @ subterm2 e1 @ subterm2 e2;
	
(*Question 8-9*)
(*Finds a c redex*)
fun is_credex (CAPP(CI,_)) =
      true
  | is_credex (CAPP(CAPP(CK, _), _)) =
      true
  | is_credex (CAPP(CAPP(CAPP(CS,_),_),_)) =
	  true
  | is_credex _ =
      false;

(*similar to above but adds app backward *)
fun caddbackapp [] e2 = []|
    caddbackapp (e1::l) e2 = (CAPP(e1,e2)):: (caddbackapp l e2);

(*similar to above but adds app forward *)
fun caddfrontapp e1 [] = []|
    caddfrontapp e1  (e2::l) = (CAPP(e1,e2)):: (caddfrontapp e1 l);
	
fun printSteps 0 = print ""
|	printSteps n = (print "\n"; print (Int.toString n); print " steps");
	
fun printlistcreduce [] 0 = ()|
    printlistcreduce (e::[]) n = (printCOM e; printSteps n) |
    printlistcreduce (e::m::l) n = (if e = m then printlistcreduce (m::l) n else
								(printCOM e; print" -->\n"; printlistcreduce (m::l) (n+1)));

	
fun creduce (CID id) =  
	[(CID id)] 
| creduce (CI) =
	[CI]
| creduce (CK) =
	[CK]
| creduce (CS) =
	[CS]
| creduce (CAPP(CI, v)) =
	[v]
| creduce (CAPP(CAPP(CK, v1), v2)) =
	[v1]
| creduce (CAPP(CAPP(CAPP(CS,v1),v2),v3)) =
	[(CAPP(CAPP(v1, v3),CAPP(v2, v3)))]
| creduce (CAPP(e1,e2)) = 
	(let val l1 = (creduce e1)
		 val l2 = (creduce e2)
		 val l3 = (caddbackapp l1 e2)
		 val l4 = (caddfrontapp (List.last l1) l2)	
		 val l7 = if l3 = l4 then l4 else (l3 @ l4)
		 val l5 = (List.last l4)
		 val l6 =  if (is_credex l5) then (l7 @ (creduce l5)) else if l7 = [l5] then [l5] else (l7 @ [l5])
		 in l6
		 end);
				
fun printcreduce e = (let val tmp =  (e::(creduce e))
		      in printlistcreduce tmp 0 end);
	
	
	
	
(*Question 10*)
(*Eta examples*)
val eta1 = (LAM("x", APP(vy,vx)));
val eta2 = (LAM("x", APP(vx,vx)));
val eta3 = (LAM("x", APP(LAM("x", APP(vy,vx)),vx)));
val eta4 = (LAM("x", APP(LAM("y", APP(vx,vy)),vx)));
val eta5 = (APP(LAM("x", APP(vy,vx)),LAM("x", APP(vy,vx))));
val eta6 = (LAM("x", APP(LAM("z", APP(LAM("y", APP(LAM("x", APP(vy,vx)),vy)),vz)),vx)));


(*Finds a eta redex*)
fun is_etaredex (LAM(v1,APP(e1,(ID v2)))) =
		if (v1 = v2) andalso (not(free v1 e1)) then	true else false
  | is_etaredex _ =
		false;
		
fun ered (LAM(v,APP(e1, e2))) = e1;
	
	
fun etareduce (ID id) = [(ID id)] |
	etareduce (APP(e1,e2)) = [((APP(e1,e2)))] |
	etareduce (LAM(v,e)) = 
		(let val l1 = if (is_etaredex (LAM(v,e))) then (etareduce (ered (LAM(v,e)))) else []
		in [LAM(v,e)]@l1 end);
		
fun printetareduce e = (let val tmp =  (etareduce e)
		      in printlistreduce tmp 0 end);
		

(*Question 11*)

(*SML Implementation of M*)
val omega = (APP(LAM("x",APP(vx, vx)), LAM("x",APP(vx, vx))));
(*SML Implementation of M'*)
val Iomega = (IAPP(ILAM("x",IAPP(Ivx,Ivx)),ILAM("x",IAPP(Ivx,Ivx))));
(*SML Implementation of M''*)
val Comega = (CAPP(CAPP(CAPP(CS,CI),CI),CAPP(CAPP(CS,CI),CI))); 
(*SML Implementation of A*)
val Bomega = (BAPP(BLAM(BAPP(Bvx,Bvx)),BLAM(BAPP(Bvx,Bvx))));
(*SML Implementation of A'*)
val IBomega = (IBAPP(IBLAM(IBAPP(IBvx,IBvx)),IBLAM(IBAPP(IBvx,IBvx))));

(*Question 13*)
val t10 = (APP(LAM("y", vz), omega));
val t11 = (APP(LAM("x", APP(APP(APP(vx, vx), vx), vx)), APP(LAM("y", vy), vz)));

(*This is the implementation of rightmost reduction*)
fun one_roreduce (ID id) = (ID id)|
    one_roreduce (LAM(id,e)) = LAM(id, (one_roreduce e))|
    one_roreduce (APP(e1,e2)) = if (has_redex e2) then  APP(e1, (one_roreduce e2)) else
                                 if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                 if (has_redex e1) then APP(one_roreduce e1, e2) else (APP(e1,e2));


fun roreduce (ID id) =  [(ID id)] |
    roreduce (LAM(id,e)) = (addlam id (roreduce e)) |
    roreduce (APP(e1,e2)) = (let val l1 = if (has_redex e2) then (roreduce (APP(e1, one_roreduce e2)))
										  else
										  if (is_redex (APP(e1,e2))) then (roreduce (red (APP(e1,e2))))
										  else
										  if (has_redex e1) then (roreduce (APP(one_roreduce e1, e2)))
										  else []
							in [APP(e1,e2)]@l1 end);


fun printroreduce e = (let val tmp =  (roreduce e)
		      in printlistreduce tmp 0 end);




