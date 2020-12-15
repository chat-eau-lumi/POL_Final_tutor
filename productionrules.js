import("types.nools");

// If the argument is an integer, return it without the ones digit, else return null
//
function removeOnesDigit(n) {
    return (Number.isInteger(n) ? Math.floor(n/10) : null);
}

// Return true if the 2 arguments are not equal.
//
function notEqual(m, n) {
    return m != n;
}


// RULE bootstrap
// Always fired at startup for initialization of working memory
//
rule bootstrap {
    when {
        s: Boolean s === false from false;
    }
    then {
        // create facts to represent the student interface components
        let listavalue = assert(new InterfaceElement("listaval"));
        let listbvalue = assert(new InterfaceElement("listbval"));
        let inputline = assert(new InterfaceElement("lineofcode"));
        let newa_0 = assert(new InterfaceElement("newa0"));
        let newa_1 = assert(new InterfaceElement("newa1"));
        let newa_2 = assert(new InterfaceElement("newa2"));
        let newb_0 = assert(new InterfaceElement("newb0"));
        let newb_1 = assert(new InterfaceElement("newb1"));
        let newb_2 = assert(new InterfaceElement("newb2"));

        // create the main Problem fact, with the given numberToSquare and the component names
        assert(new Problem("square"+numberToSquare, numberToSquare,
            firstPart.name,
            firstPartPlus1.name,
            product.name,
            append25.name,
            finalAnswer.name));

        // write the numberToSquare to the proper student interface component
        assert(new TPA(given.name, "UpdateTextField", numberToSquare));

        setProblemAttribute("use_backtracking", true);
        halt();
    }
}

// RULE findFirstPart
// IF
//   there is a Problem with givenNumber n that ends in 5
//   and whose firstPart is empty  (i.e., we have not yet found the first part)
// THEN
//   compute f by removing the ones digit from n
//   write f as the firstPart
//
rule findFirstPart {
    when {
        prob : Problem prob.firstPart == null && (prob.givenNumber % 10) == 5
            {givenNumber: n, ieFirstPart: sel};
        ie : InterfaceElement ie.name == sel && ie.value == null;
    }
    then {
            // compute the number with the 5 on the right "chopped off"
        let f = removeOnesDigit(n);
            // hints
        assert(new Hint("Start by removing the right-most digit from "+n+"."));
        assert(new Hint("If you remove the right-most digit from "+n+", you have "+f+"."));
        assert(new Hint("Please write "+f+"."));
            // model observable action
	      if (checkSAI({selection: sel, action: "UpdateTextField", input: f})) {
             modify(prob, "firstPart", f);    // modify semantic representation
	           modify(ie, "value", f);         // modify interface represention in WM
                                            //(this does not change the interface itself!!)
	           halt();                 // await next student action
        } 
        else if(checkSAI({selection: sel, action: "UpdateTextField", input: 5}, null, true)) {
            setSuccessOrBugMsg("Incorrect- remove the other part of the number.");
            backtrack();
        }
        else {
            backtrack();             // undo any changes and search further
	     }
    }
}

// RULE addOne
// IF
//    there is a goal to determine the square of a number
//    and we have split off the first part (call it f)
//    and we have not added 1 to the first part
//THEN
//    Write (f + 1) as the first part plus 1

rule addOne {
  when {
    p : Problem p.firstPart != null && p.firstPartPlus1 == null
	      {firstPart: f, ieFirstPartPlus1: sel};
    ie : InterfaceElement ie.name==sel && ie.value==null;    
  }
  then {
            // do the actual adding of 1
    let f1 = f + 1;
            // hints
    assert(new Hint("Next step: Add 1."));
    assert(new Hint("If you add 1 to the previous number, "+f+", you have "+f1+"."));
    assert(new Hint("Please write "+f1+"."));
            // model observable action
    if(checkSAI({selection: sel, action: "UpdateTextField", input: f1})) {
        modify(p, "firstPartPlus1", f1);       // modify semantic representation
        modify(ie, "value", f1);              // modify interface represention in WM
                                            //(this does not change the interface itself!!)
        halt();                 // await next student action
    }
    else {
	     backtrack();             // undo any changes and search further
	 }
  }
}

// RULE getProduct
// IF
//    there is a goal to determine the square of a number
//    and we have split off the first part (call it f)
//    and we have added 1 to the first part
//    and we have not multiplied f and (f + 1)
//THEN
//    Write pro = f(f + 1)

rule getProduct {
    when {
      p : Problem p.firstPart != null && p.firstPartPlus1 != null && p.product == null
            {firstPart: f, firstPartPlus1: f1, ieProduct: sel};
      ie : InterfaceElement ie.name==sel && ie.value==null;    
    }
    then {
              // get the product
      let pro = f * f1;
              // hints
      assert(new Hint("Next step: Multiply the two above numbers."));
      assert(new Hint("If you multiply "+f+" by "+f1+", you get "+pro+"."));
      assert(new Hint("Please write "+pro+"."));
              // model observable action
      if(checkSAI({selection: sel, action: "UpdateTextField", input: pro})) {
          modify(p, "product", pro);       // modify semantic representation
          modify(ie, "value", pro);              // modify interface represention in WM
                                              //(this does not change the interface itself!!)
          halt();                 // await next student action
      }
      else {
           backtrack();             // undo any changes and search further
        }
    }
}

// RULE append25
// IF
//    there is a goal to determine the square of a number
//    and we have split off the first part (call it f)
//    and we have added 1 to the first part
//    and we have multiplied f and (f + 1) (call it pro)
//    and we have not appended 25 to the product
//THEN
//    Write res as 25 appended to the product

rule append25 {
    when {
      p : Problem p.firstPart != null && p.firstPartPlus1 != null 
      && p.product != null && p.append25 == null
            {firstPart: f, firstPartPlus1: f1, product: pro, ieAppend25: sel};
      ie : InterfaceElement ie.name==sel && ie.value==null;    
    }
    then {
              // get the result
      let res = (pro * 100) + 25;
              // hints
      assert(new Hint("Next step: Append 25 to the product."));
      assert(new Hint("If you append 25 to "+pro+", you get "+res+"."));
      assert(new Hint("Please write "+res+"."));
              // model observable action
      if(checkSAI({selection: sel, action: "UpdateTextField", input: res})) {
          modify(p, "append25", res);       // modify semantic representation
          modify(ie, "value", res);              // modify interface represention in WM
                                              //(this does not change the interface itself!!)
          halt();                 // await next student action
      }
      else if(checkSAI({selection: sel, action: "UpdateTextField", input: pro + 25}, null, true)) {
            setSuccessOrBugMsg("Incorrect- append 25, don't add it.");
            backtrack();
      }
      else {
           backtrack();             // undo any changes and search further
        }
    }
}

// RULE getFinalAnswer
// IF
//    there is a goal to determine the square of a number
//    and we have split off the first part (call it f)
//    and we have added 1 to the first part
//    and we have multiplied f and (f + 1) (call it pro)
//    and we have appended 25 to the product (call it res)
//    and we have not marked this answer as the final answer
//THEN
//    Write res in the final answer box

rule getFinalAnswer {
    when {
      p : Problem p.firstPart != null && p.firstPartPlus1 != null 
      && p.product != null && p.append25 != null && p.finalAnswer == null
            {firstPart: f, firstPartPlus1: f1, product: pro, append25: res, ieFinalAnswer: sel};
      ie : InterfaceElement ie.name==sel && ie.value==null;    
    }
    then {
              // hints
      assert(new Hint("Next step: You've done all the work. What's the answer you just got?"));
      assert(new Hint("Please write "+res+"."));
              // model observable action
      if(checkSAI({selection: sel, action: "UpdateTextField", input: res})) {
          modify(p, "finalAnswer", res);       // modify semantic representation
          modify(ie, "value", res);              // modify interface represention in WM
                                              //(this does not change the interface itself!!)
          halt();                 // await next student action
      }
      else {
           backtrack();             // undo any changes and search further
        }
    }
}

rule clickDone {
    when {
        p: Problem p.finalAnswer != null
    }

    then {
        let predictedSAI = {
            selection: "done",
            action: "ButtonPressed",
            input: "don't_care"
        };

        if (checkSAI(predictedSAI)) {
            setSuccessOrBugMsg("You're done!");
            halt();
        } else {
            backtrack();
        }
    }
}