package comp0012.main;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.InstructionFinder;



public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;

	JavaClass original = null;
	JavaClass optimized = null;

	public ConstantFolder(String classFilePath)
	{
		try{
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
		} catch(IOException e){
			e.printStackTrace();
		}
	}
	
	public void optimize()
	{
		ClassGen cgen = new ClassGen(this.original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		// Implement your optimization here
		cgen.setMajor(50);
		
		System.out.println("\n\n\n\nOptimizing Class: " + cgen.getClassName());

		Method[] methods = cgen.getMethods();

		//Optimize all methods
		for (Method method : methods) {
			System.out.println("\n\n\nOptimizing method: " + method.getName());
			optimizeMethod(cgen, cpgen, method);
		}
        
		this.optimized = cgen.getJavaClass();
	}

	private void optimizeMethod(ClassGen cgen, ConstantPoolGen cpgen, Method method) {
		MethodGen methodGen = new MethodGen(method, cgen.getClassName(), cpgen);

		//Get all instruction in the method
		InstructionList il = methodGen.getInstructionList();

		simpleFolding(cgen, cpgen, il);
		constantVariableFolding(cgen, cpgen, il);
		dynamicVariableFolding(cgen, cpgen, il);
		deadCodeElimination(cgen, cpgen, il);

		il.setPositions(true);

		methodGen.setMaxStack();
		methodGen.setMaxLocals();

		methodGen.setInstructionList(il);
		Method newMethod = methodGen.getMethod();

		//Replace the original method
		cgen.replaceMethod(method, newMethod);
	}
	
	private void simpleFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList il) {
		System.out.println("\nDoing SimpleFolding.");

		boolean optimised;
		do{
			InstructionFinder instructionFinder = new InstructionFinder(il);

			//Find all simple calculation
			String calculationPattern = "(LDC|LDC2_W|ConstantPushInstruction) ConversionInstruction? (LDC|LDC2_W|ConstantPushInstruction) ConversionInstruction? ArithmeticInstruction";

			optimised = false;
			for(Iterator iterator1 = instructionFinder.search(calculationPattern); iterator1.hasNext();){
				InstructionHandle[] match1 = (InstructionHandle[]) iterator1.next();

				Number leftNumber = null;
				Number rightNumber = null;
				ArithmeticInstruction operator = null;

				//May exist type conversion
				ConversionInstruction conversionInstruction1 = null;
				ConversionInstruction conversionInstruction2 = null;

				int index = 0;

				//Get leftNumber
				leftNumber = getInstructionValue(match1[index], cpgen);
				index++;

				//Check for conversion
				if(match1[index].getInstruction() instanceof ConversionInstruction){
					conversionInstruction1 = (ConversionInstruction) match1[index].getInstruction();
					index++;
				}

				//Get rightNumber
				rightNumber = getInstructionValue(match1[index], cpgen);
				index++;

				//Check for conversion
				if(match1[index].getInstruction() instanceof ConversionInstruction){
					conversionInstruction2 = (ConversionInstruction) match1[index].getInstruction();
					index++;
				}

				//Check operator type: add sub mul div...
				if(match1[index].getInstruction() instanceof ArithmeticInstruction){
					operator = (ArithmeticInstruction) match1[index].getInstruction();
				}
				Type operatorType = operator.getType(cpgen);
				String arithmeticType = operator.getName().substring(1);

				System.out.println(" LeftNumber: " + leftNumber + " RightNumber: " + rightNumber + " Variable Type: " + operatorType + " Arithmetic Type: " + arithmeticType);

				Number foldedValue = arithmeticCalculator(leftNumber, rightNumber, arithmeticType, operatorType);

				if(foldedValue != null){
					System.out.println("Folded to: " + foldedValue);

					// The index of the new value
					int cpFoldedValueIndex = -1;

					// Add result to constant pool.
					if(operatorType == Type.INT){
						cpFoldedValueIndex = cpgen.addInteger(foldedValue.intValue());
					}else if(operatorType == Type.FLOAT){
						cpFoldedValueIndex = cpgen.addFloat(foldedValue.floatValue());
					}else if(operatorType == Type.LONG){
						cpFoldedValueIndex = cpgen.addLong(foldedValue.longValue());
					}else if(operatorType == Type.DOUBLE){
						cpFoldedValueIndex = cpgen.addDouble(foldedValue.doubleValue());
					}

					System.out.println("Folded value index in constant pool: " + cpFoldedValueIndex);

					if(cpFoldedValueIndex > -1){
						//Insert folded value instruction

						if(operatorType == Type.INT || operatorType == Type.FLOAT){
							il.insert(match1[0], new LDC(cpFoldedValueIndex));
						}else if(operatorType == Type.LONG || operatorType == Type.DOUBLE){
							il.insert(match1[0], new LDC2_W(cpFoldedValueIndex));
						}

						try{
							//Delete the original instruction
							il.delete(match1[0], match1[index]);
						}catch(TargetLostException e){
							System.out.println("Simple folding fail.");
							e.printStackTrace();
						}

						optimised = true;
						System.out.println("Optimization performed.");
					}else{
						System.out.println("Fail to add folded value to constant pool.");
					}

				}else{
					System.out.print("Folded fail. Unknown type: ");
					System.out.println(operatorType);
				}

			}
		}while(optimised);
	}

	private void constantVariableFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList il){
		System.out.println("\n\nDoing Constant Variable Folding.");

		// This hashmap stores all literal values that we know about.
		HashMap<Integer,Number> constantsValues = new HashMap<>();

		//It contains all variable which is not reassigned in this method
		HashMap<Integer, Boolean> constants = new HashMap<>();

		//set true for constant, false for reassigned variable in HashMap constants
		InstructionFinder instructionFinder = new InstructionFinder(il);
		String pattern1 = "StoreInstruction | IINC";
		for(Iterator iterator1 = instructionFinder.search(pattern1); iterator1.hasNext();){
			InstructionHandle[] match1 = (InstructionHandle[]) iterator1.next();

			if(match1[0].getPosition() > il.getEnd().getPosition()){
				continue;
			}

			//Get the index of the stored variable.
			int localVariableIndex = ((LocalVariableInstruction) match1[0].getInstruction()).getIndex();

			if (!constants.containsKey(localVariableIndex)) {
				//add a new value
				constants.put(localVariableIndex, true);
			} else {
				//it is reassigned, not a constant
				constants.put(localVariableIndex, false);
			}
		}

		//Do constant folding for each decleared variable(not for iinc)
		boolean couldFolded;
		do{
			//Store all constants
			instructionFinder = new InstructionFinder(il);
			String pattern2 = "(LDC | LDC2_W| ConstantPushInstruction) (DSTORE | FSTORE | ISTORE | LSTORE)";
			for(Iterator iterator2 = instructionFinder.search(pattern2); iterator2.hasNext();){
				InstructionHandle[] match2 = (InstructionHandle[]) iterator2.next();

				StoreInstruction storeInstruction = (StoreInstruction) match2[1].getInstruction();

				//Look for constants, not need variable
				if(!constants.containsKey(storeInstruction.getIndex()) || !constants.get(storeInstruction.getIndex())){
					continue;
				}

				//Get constant value
				Number literalValue = getInstructionValue(match2[0], cpgen);

				System.out.print("Constants index: ");
				System.out.println(storeInstruction.getIndex());
				System.out.print("Constants value: ");
				System.out.println(literalValue);

				//Collect all constant index and value
				constantsValues.put(storeInstruction.getIndex(), literalValue);
			}

			couldFolded = false;

			instructionFinder = new InstructionFinder(il);
			String pattern3 = "LoadInstruction";
			for(Iterator iterator3 = instructionFinder.search(pattern3); iterator3.hasNext();){
				InstructionHandle[] match3 = (InstructionHandle[]) iterator3.next();
				LoadInstruction loadInstruction = (LoadInstruction) match3[0].getInstruction();

				//check if it load a constant, if it is a constant replace it with it's value
				if (constantsValues.containsKey(loadInstruction.getIndex())) {

					System.out.print("Load a constant with index: ");
					System.out.println(loadInstruction.getIndex());

					Number constantToReplace = constantsValues.get(loadInstruction.getIndex());

					//Add new constant to constant pool
					Instruction addConstantInstruction = addToConstantPool(loadInstruction, constantToReplace, cpgen);

					//Add the instruction
					il.insert(match3[0], addConstantInstruction);

					try {
						//Delete the original instruction
						il.delete(match3[0]);
					} catch (TargetLostException e) {
						e.printStackTrace();
					}

					couldFolded = true;

					System.out.print("replace it with value: ");
					System.out.println(constantToReplace.doubleValue());
				}
			}

			//Do simple folding to get the optimized intruction, so we could obtain new constant next time
			simpleFolding(cgen, cpgen, il);
		}while(couldFolded);

	}

	private void dynamicVariableFolding(ClassGen cgen, ConstantPoolGen cpgen, InstructionList il) {
		System.out.println("\n\nDoing Dynamic variable Folding.");

		//Store current variable
		HashMap<Integer, Number> variable = new HashMap<>();

		//Mark current position
		InstructionHandle currentInstructionHandle = il.getStart();

		//Store loop information
		ArrayList<InstructionHandle> loopEnds = new ArrayList<>();

		il.setPositions(true);

		//Find all loops
		InstructionFinder loopFinder = new InstructionFinder(il);
		String loopPattern = "GotoInstruction";
		for(Iterator loopIterator = loopFinder.search(loopPattern); loopIterator.hasNext();){
			loopEnds.add(((InstructionHandle[]) loopIterator.next())[0]);
		}

		do{
			InstructionFinder instructionFinder = new InstructionFinder(il);
			String variableDeclarePattern = "(LDC | LDC2_W | ConstantPushInstruction) (DSTORE | FSTORE | ISTORE | LSTORE)";
			Iterator variableDeclareIterator = instructionFinder.search(variableDeclarePattern, currentInstructionHandle);

			//Do dynamic folding for variable one by one
			if(variableDeclareIterator.hasNext()){
				InstructionHandle[] declareMatched = (InstructionHandle[]) variableDeclareIterator.next();

				//Move currentInstructionHandle behind first declared variable, so next time, we get a new declared variable
				currentInstructionHandle = declareMatched[1];

				System.out.print("Current position: ");
				System.out.println(currentInstructionHandle.getPosition());

				StoreInstruction storeInstruction = (StoreInstruction) declareMatched[1].getInstruction();

				//Get the index of this variable
				int localVariableIndex = storeInstruction.getIndex();

				Number literalValue = getInstructionValue(declareMatched[0], cpgen);

				System.out.print("Dynamic folding for index ");
				System.out.print(storeInstruction.getIndex());
				System.out.print(" with value ");
				System.out.println(literalValue.doubleValue());

				//Store index and value
				variable.put(localVariableIndex, literalValue);

				InstructionHandle reassignmentInstructionHandle = null;
				boolean notReasigned = true;

				//Check for reassignments, if iinc occurs, we put it into a HashMaps with position and increment
				HashMap<Integer, Integer> increments = new HashMap<>();
				if(currentInstructionHandle.getNext() != null){
					String reassignmentPattern = "StoreInstruction | IINC";
					for(Iterator reassignmentIterator = instructionFinder.search(reassignmentPattern, currentInstructionHandle.getNext()); reassignmentIterator.hasNext();){
						InstructionHandle[] reassigmentMatched = (InstructionHandle[]) reassignmentIterator.next();

						if(reassigmentMatched[0].getInstruction() instanceof StoreInstruction){

							//if reassignment for this variable occurs, we make a mark
							if(((StoreInstruction) reassigmentMatched[0].getInstruction()).getIndex() == localVariableIndex){
								reassignmentInstructionHandle = reassigmentMatched[0];

								//if reassignment occurs, we break for loop, and optimise code before this instruction
								notReasigned = false;
								break;
							}

						}else if(reassigmentMatched[0].getInstruction() instanceof IINC){

							//if iinc for this variable occurs, we make a mark
							if(((IINC) reassigmentMatched[0].getInstruction()).getIndex() == localVariableIndex){
								reassignmentInstructionHandle = reassigmentMatched[0];

								//we store this iinc instruction position and value
								increments.put(reassigmentMatched[0].getPosition(), ((IINC) reassigmentMatched[0].getInstruction()).getIncrement());
							}

						}

					}

					//if this variable is never reassignment, we do not need a mark
					if(notReasigned){
						reassignmentInstructionHandle = null;
					}

				}

				//Replace all load intruction before reassignment for this variable
				String loadPattern = "LoadInstruction";
				for(Iterator loadIterator = instructionFinder.search(loadPattern, currentInstructionHandle); loadIterator.hasNext();){
					InstructionHandle[] loadMatched = (InstructionHandle[]) loadIterator.next();

					LoadInstruction loadInstruction = (LoadInstruction) loadMatched[0].getInstruction();
					//we only look into this variable
					if(withinLoop(loadMatched[0], loopEnds) || loadInstruction.getIndex() != localVariableIndex){
						continue;
					}

					if(reassignmentInstructionHandle != null && loadMatched[0].getPosition() > reassignmentInstructionHandle.getPosition()){
						break;
					}

					if(variable.containsKey(loadInstruction.getIndex())){

						Number constantToReplace = variable.get(loadInstruction.getIndex());

						//we check for iinc, add all iinc in this scope to the new value
						for(Integer key : increments.keySet()){
							if(loadMatched[0].getPosition() > key){
								Integer increment = increments.get(key);
								if(constantToReplace instanceof Double) {
									constantToReplace = constantToReplace.doubleValue() + increment;
								} else if(constantToReplace instanceof Float) {
									constantToReplace = constantToReplace.floatValue() + increment;
								} else if(constantToReplace instanceof Long) {
									constantToReplace = constantToReplace.longValue() + increment;
								} else if(constantToReplace instanceof Integer){
									constantToReplace = constantToReplace.intValue() + increment;
								}
							}
						}

						//Add new constant to constant pool
						Instruction addConstantInstruction = addToConstantPool(loadInstruction, constantToReplace, cpgen);

						//insert it before load
						il.insert(loadMatched[0], addConstantInstruction);

						try{
							//Delete the original instruction
							il.delete(loadMatched[0]);
						}catch(TargetLostException e){
							e.printStackTrace();
						}

						il.setPositions(true);

						System.out.print("Repelace variable index: ");
						System.out.print(loadInstruction.getIndex());
						System.out.print(" with value ");
						System.out.print(literalValue.doubleValue());
					}
				}

				//Do simplefolding, so it could do arithmatic calculation use the new value we add
				simpleFolding(cgen, cpgen, il);

				il.setPositions(true);

				currentInstructionHandle = currentInstructionHandle.getNext();
			}else{
				//we have no variable declared
				break;
			}

		}while(true);
	}

	//Do dead code elimination, we remove the reassignment for variable that is never used
	private void deadCodeElimination(ClassGen cgen, ConstantPoolGen cpgen, InstructionList il){
		System.out.println("\nDoing DeadCode Elimination.");
		System.out.println("Remove all intruction of a dead variable except declaration.");

		//Mark current position
		InstructionHandle currentInstructionHandle = il.getStart();

		il.setPositions(true);

		do{
			InstructionFinder instructionFinder = new InstructionFinder(il);
			String variableDeclarePattern = "(LDC | LDC2_W | ConstantPushInstruction) StoreInstruction";
			Iterator variableDeclareIterator = instructionFinder.search(variableDeclarePattern, currentInstructionHandle);

			//Do dead code elimination for variable one by one
			if(variableDeclareIterator.hasNext()){
				InstructionHandle[] declareMatched = (InstructionHandle[]) variableDeclareIterator.next();

				//Move currentInstructionHandle behind first declared variable, so next time, we get next declared variable
				currentInstructionHandle = declareMatched[1];

				//Get the index of this variable
				int localVariableIndex = ((StoreInstruction) declareMatched[1].getInstruction()).getIndex();

				//this variable has been optimized fully, so we have a check if it is loaded
				boolean notloaded = true;
				String loadPattern = "LoadInstruction";
				for(Iterator loadIterator = instructionFinder.search(loadPattern, currentInstructionHandle); loadIterator.hasNext();){
					InstructionHandle[] loadMatched = (InstructionHandle[]) loadIterator.next();

					LoadInstruction loadInstruction = (LoadInstruction) loadMatched[0].getInstruction();
					//we only look into this variable
					if(loadInstruction.getIndex() == localVariableIndex){
						notloaded = false;
					}
				}

				//if it is not loaded, we remove all instruction except declare
				if(notloaded){

					//remove reassignment
					String reassignmentPattern = "(LDC | LDC2_W | ConstantPushInstruction) StoreInstruction";
					for(Iterator reassignmentIterator = instructionFinder.search(reassignmentPattern, currentInstructionHandle.getNext()); reassignmentIterator.hasNext();){
						InstructionHandle[] reassigmentMatched = (InstructionHandle[]) reassignmentIterator.next();
						//if reassignment for this variable occurs, we delete it
						if(((StoreInstruction) reassigmentMatched[1].getInstruction()).getIndex() == localVariableIndex){
							try{
								il.delete(reassigmentMatched[0]);
								il.delete(reassigmentMatched[1]);
							}catch(TargetLostException e){
								e.printStackTrace();
							}
						}
					}

					//remove iinc
					String iincPattern = "IINC";
					for(Iterator iincIterator = instructionFinder.search(iincPattern, currentInstructionHandle.getNext()); iincIterator.hasNext();){
						InstructionHandle[] iincMatched = (InstructionHandle[]) iincIterator.next();
						if(((IINC) iincMatched[0].getInstruction()).getIndex() == localVariableIndex){
							try{
								il.delete(iincMatched[0]);
							}catch(TargetLostException e){
								e.printStackTrace();
							}
						}
					}
				}

				/*
				try{
					il.delete(declareMatched[0]);
					il.delete(declareMatched[1]);
				}catch(TargetLostException e){
					e.printStackTrace();
				}
				 */

				il.setPositions(true);
				//look into next codes
				currentInstructionHandle = currentInstructionHandle.getNext();
			}else{
				break;
			}
		}while(true);
	}

	//Do arithmetic calculation
	private Number arithmeticCalculator(Number leftNumber, Number rightNumber, String operationStr, Type operatorType){
		Number result = null;
		switch(operationStr){
			case "add":
				if(operatorType == Type.INT){
					result = leftNumber.intValue() + rightNumber.intValue();
				}else if(operatorType == Type.LONG){
					result = leftNumber.longValue() + rightNumber.longValue();
				}else if(operatorType == Type.FLOAT){
					result = leftNumber.floatValue() + rightNumber.floatValue();
				}else if(operatorType == Type.DOUBLE){
					result = leftNumber.doubleValue() + rightNumber.doubleValue();
				}
				break;
			case "sub":
				if(operatorType == Type.INT){
					result = leftNumber.intValue() - rightNumber.intValue();
				}else if(operatorType == Type.LONG){
					result = leftNumber.longValue() - rightNumber.longValue();
				}else if(operatorType == Type.FLOAT){
					result = leftNumber.floatValue() - rightNumber.floatValue();
				}else if(operatorType == Type.DOUBLE){
					result = leftNumber.doubleValue() - rightNumber.doubleValue();
				}
				break;
			case "mul":
				if(operatorType == Type.INT){
					result = leftNumber.intValue() * rightNumber.intValue();
				}else if(operatorType == Type.LONG){
					result = leftNumber.longValue() * rightNumber.longValue();
				}else if(operatorType == Type.FLOAT){
					result = leftNumber.floatValue() * rightNumber.floatValue();
				}else if(operatorType == Type.DOUBLE){
					result = leftNumber.doubleValue() * rightNumber.doubleValue();
				}
				break;
			case "div":
				if(operatorType == Type.INT){
					result = leftNumber.intValue() / rightNumber.intValue();
				}else if(operatorType == Type.LONG){
					result = leftNumber.longValue() / rightNumber.longValue();
				}else if(operatorType == Type.FLOAT){
					result = leftNumber.floatValue() / rightNumber.floatValue();
				}else if(operatorType == Type.DOUBLE){
					result = leftNumber.doubleValue() / rightNumber.doubleValue();
				}
				break;
		}
		return result;
	}

	//Get the value in the instruction
	private Number getInstructionValue(InstructionHandle instructionHandle, ConstantPoolGen cpgen){
		if(instructionHandle.getInstruction() instanceof ConstantPushInstruction){
			return ((ConstantPushInstruction) instructionHandle.getInstruction()).getValue();
		}else if(instructionHandle.getInstruction() instanceof LDC){
			return (Number) ((LDC) instructionHandle.getInstruction()).getValue(cpgen);
		}else if(instructionHandle.getInstruction() instanceof LDC2_W){
			return (Number) ((LDC2_W) instructionHandle.getInstruction()).getValue(cpgen);
		}else{
			return null;
		}
	}

	//check if a intruction is in a loop
	private boolean withinLoop(InstructionHandle currentInstructionHandle, ArrayList<InstructionHandle> loopEnds){
		for(InstructionHandle loopEnd : loopEnds){
			InstructionHandle loopStart = ((GotoInstruction) loopEnd.getInstruction()).getTarget();
			int position = currentInstructionHandle.getPosition();

			if(position >= loopStart.getPosition() && position <= loopEnd.getPosition()){
				return true;
			}
		}
		return false;
	}

	private Instruction addToConstantPool(LoadInstruction loadInstruction, Number literalValueToReplace, ConstantPoolGen cpgen){
		Instruction addConstantInstruction = null;

		if(loadInstruction.getType(cpgen) == Type.INT){
			if(Math.abs(literalValueToReplace.intValue()) < Byte.MAX_VALUE){
				addConstantInstruction = new BIPUSH(literalValueToReplace.byteValue());
			}else if(Math.abs(literalValueToReplace.intValue()) < Short.MAX_VALUE){
				addConstantInstruction = new SIPUSH(literalValueToReplace.shortValue());
			}else{
				addConstantInstruction = new LDC(cpgen.addInteger(literalValueToReplace.intValue()));
			}
		}else if(loadInstruction.getType(cpgen) == Type.FLOAT){
			addConstantInstruction = new LDC(cpgen.addFloat(literalValueToReplace.floatValue()));
		}else if (loadInstruction.getType(cpgen) == Type.DOUBLE){
			addConstantInstruction = new LDC2_W(cpgen.addDouble(literalValueToReplace.doubleValue()));
		}else if (loadInstruction.getType(cpgen) == Type.LONG){
			addConstantInstruction = new LDC2_W(cpgen.addLong(literalValueToReplace.longValue()));
		}

		return addConstantInstruction;
	}
	
	public void write(String optimisedFilePath)
	{
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
	}

}