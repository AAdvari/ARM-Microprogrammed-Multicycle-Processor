module modified_mc(input  logic        clk, reset,  
           output logic [31:0] WriteData, Adr,  
           output logic        MemWrite); 
 
  logic [31:0] ReadData; 
   
  // instantiate processor and shared memory 
  arm arm(clk, reset, MemWrite, Adr,  
          WriteData, ReadData); 
  mem mem(clk, MemWrite, Adr, WriteData, ReadData);
endmodule 



module arm(input  logic        clk, reset, 
           output logic        MemWrite, 
           output logic [31:0] Adr, WriteData, 
           input  logic [31:0] ReadData); 
 
  logic [31:0] Instr; 
  logic [3:0]  ALUFlags; 
  logic        PCWrite, RegWrite, IRWrite; 
  logic        AdrSrc, ALUSrcA; 
  logic [1:0]  RegSrc, ALUSrcB, ImmSrc, ALUControl, ResultSrc; 
 
  controller c(clk, reset, Instr[31:12], ALUFlags,  
               PCWrite, MemWrite, RegWrite, IRWrite, 
               AdrSrc, RegSrc, ALUSrcA, ALUSrcB, ResultSrc, 
               ImmSrc, ALUControl); 
  datapath dp(clk, reset, Adr, WriteData, ReadData, Instr, ALUFlags, 
              PCWrite, RegWrite, IRWrite, 
              AdrSrc, RegSrc, ALUSrcA, ALUSrcB, ResultSrc, 
              ImmSrc, ALUControl); 
endmodule 



module datapath(input  logic        clk, reset, 
                output logic [31:0] Adr, WriteData, 
                input  logic [31:0] ReadData, 
                output logic [31:0] Instr, 
                output logic [3:0]  ALUFlags, 
                input  logic        PCWrite, RegWrite, 
                input  logic        IRWrite, 
                input  logic        AdrSrc,  
                input  logic [1:0]  RegSrc,  
                input  logic        ALUSrcA, 
                input  logic [1:0]  ALUSrcB, ResultSrc, 
                input  logic [1:0]  ImmSrc, ALUControl); 
 
  logic [3:0]  RA1, RA2;
  logic [31:0] Data, RD1, RD2, A, ALUResult, ALUOut,PCNext, PC,ExtImm, SrcA, SrcB, Result;
 
  
  flopenr #(32) pc_flopenr(clk, reset, PCWrite, Result, PC);  // PC' (Result) to Pc
   
  
  mux2 #(32)    Adr_mux2(PC, Result, AdrSrc, Adr);  // PC & Result mux with 2 input befor Memory
  flopenr #(32) Instr_flopenr(clk, reset, IRWrite, ReadData, Instr);  // RD (ReadData) to Instr
  flopr   #(32) ReadData_flopr(clk, reset, ReadData, Data);  // RD (ReadData) to Data
   
  
  mux2 #(4)   RA1_mux2(Instr[19:16], 4'b1111, RegSrc[0], RA1);  // Instr[19:16] & 15 mux with 2 input befor Register File
  mux2 #(4)   RA2_mux2(Instr[3:0], Instr[15:12], RegSrc[1], RA2);  // Instr[3:0] & Instr[15:12] mux with 2 input befor Register File
  regfile     Register_File(clk, RegWrite, RA1, RA2, 
                 Instr[15:12], Result, Result,  
                 RD1, RD2);  // Register File
  flopr #(32) RD1_flopr(clk, reset, RD1, A);  // RD1 to A flopr
  flopr #(32) RD2_flopr(clk, reset, RD2, WriteData);  // RD2 to Write Data flopr
  extend      Extend(Instr[23:0], ImmSrc, ExtImm);  // Extend
 
  
  mux2 #(32)  SrcA_mux2(A, PC, ALUSrcA, SrcA);  // PC & A mux with 2 input befor ALU
  mux3 #(32)  SrcB_mux3(WriteData, ExtImm, 32'd4, ALUSrcB, SrcB);  // WriteData & Extlmm & 4 mux with 3 input befor ALU
  alu         ALU(SrcA, SrcB, ALUControl, ALUResult, ALUFlags);  // ALU
  flopr #(32) ALUResult_flopr(clk, reset, ALUResult, ALUOut);  // ALUResult to ALUOut flopr
  mux3 #(32)  Result_mux3(ALUOut, Data, ALUResult, ResultSrc, Result);  // ALUOut & Data & ALUResult mux with 3 input after ALU & flopr
endmodule 



module extend(input  logic [23:0] Instr, 
              input  logic [1:0]  ImmSrc, 
              output logic [31:0] ExtImm); 
  
  always_comb 
    case(ImmSrc)  
               // 8-bit unsigned immediate 
      2'b00:   ExtImm = {24'b0, Instr[7:0]};   
               // 12-bit unsigned immediate  
      2'b01:   ExtImm = {20'b0, Instr[11:0]};  
               // 24-bit two's complement shifted branch  
      2'b10:   ExtImm = {{6{Instr[23]}}, Instr[23:0], 2'b00};  
      default: ExtImm = 32'bx; // undefined 
    endcase              
endmodule 


module regfile(input  logic        clk,  
               input  logic        we3,  
               input  logic [3:0]  ra1, ra2, wa3,  
               input  logic [31:0] wd3, r15, 
               output logic [31:0] rd1, rd2); 
 
  logic [31:0] rf[14:0]; 
 
 
  always_ff @(posedge clk) 
    if (we3) rf[wa3] <= wd3;  
 
  assign rd1 = (ra1 == 4'b1111) ? r15 : rf[ra1]; 
  assign rd2 = (ra2 == 4'b1111) ? r15 : rf[ra2]; 
endmodule 




module mem(input  logic        clk, we, 
           input  logic [31:0] a, wd, 
           output logic [31:0] rd); 
 
  logic [31:0] RAM[63:0]; 
 
  initial 
      $readmemh("C:/Users/parsa/Desktop/Memari_Project_FinalEdit/memfile.dat",RAM); 
 
  assign rd = RAM[a[31:2]]; // word aligned 
 
  always_ff @(posedge clk) 
    if (we) RAM[a[31:2]] <= wd; 
endmodule 





module controller(input  logic         clk,
                  input  logic         reset,
                  input  logic [31:12] Instr,
                  input  logic [3:0]   ALUFlags,
						
                  output logic         PCWrite,
                  output logic         MemWrite,
                  output logic         RegWrite,
                  output logic         IRWrite,
                  output logic         AdrSrc,
                  output logic [1:0]   RegSrc,
                  output logic         ALUSrcA,
                  output logic [1:0]   ALUSrcB,
                  output logic [1:0]   ResultSrc,
                  output logic [1:0]   ImmSrc,
                  output logic [1:0]   ALUControl);
        logic [1:0] FlagW;
		  logic PCS, NextPC, RegW, MemW;
	
  decode decoder(clk, reset, Instr[27:26], Instr[25:20], Instr[15:12],
             FlagW, PCS, NextPC, RegW, MemW,
             IRWrite, AdrSrc, ResultSrc, ALUSrcA, 
             ALUSrcB, ImmSrc, RegSrc, ALUControl);
				 
  condlogic condlog(clk, reset, Instr[31:28], ALUFlags,
               FlagW, PCS, NextPC, RegW, MemW,
               PCWrite, RegWrite, MemWrite);            
		

endmodule



module decode(input  logic       clk, reset,
              input  logic [1:0] Op,
              input  logic [5:0] Funct,
              input  logic [3:0] Rd,
              output logic [1:0] FlagW,
              output logic       PCS, NextPC, RegW, MemW,
              output logic       IRWrite, AdrSrc,
              output logic [1:0] ResultSrc,
				  output logic       ALUSrcA,
				  output logic [1:0] ALUSrcB, 
              output logic [1:0] ImmSrc, RegSrc, ALUControl);

  // ADD CODE HERE
  // Implement a microprogrammed controller
  // using a control memory (ROM).
  logic Branch,ALUOp;
  
  
  
	//ALU Decoder
  	always_comb
		if (ALUOp) 
			begin
				case(Funct[4:1])
					4'b0100: ALUControl = 2'b00; // ADD
					4'b0010: ALUControl = 2'b01; // SUB
					4'b0000: ALUControl = 2'b10; // AND
					4'b1100: ALUControl = 2'b11; // ORR
					default: ALUControl = 2'bXX; // unimplemented
				endcase

				FlagW[1] = Funct[0];
				FlagW[0] = Funct[0] & (ALUControl == 2'b00 | ALUControl == 2'b01);
			end 
		else 
			begin
				ALUControl = 2'b00; // add for non-DP instructions
				FlagW = 2'b00; // don't update Flags
			end
			
			
			
	//PC Logic
	assign PCS = ((Rd == 4'b1111) & RegW) | Branch;
  
  
  
  
	// Instr Decoder 
	assign RegSrc = Op == 2'b00 ? (Funct[5] == 1'b1 ? 2'bX0 : 2'b00) : 
								(Op == 2'b01 ? (Funct[0] == 1'b1 ? 2'bX0 : 2'b10) : 
									(Op == 2'b10 ? 2'bX1 : 2'bXX));
	assign ImmSrc = Op;
	
	
	
	// Microprogrammed Control
	mpControl mpc(clk,reset,Op,Funct,NextPC,RegW,MemW,IRWrite,AdrSrc,ALUSrcA,Branch,ALUOp,ResultSrc,ALUSrcB);
		
endmodule


module mpControl(input logic clk, reset,
				   input logic [1:0] Op,
				   input logic [5:0] Funct,
				   output logic NextPC, RegW, MemW, IRWrite, AdrSrc, ALUSrcA, Branch, ALUOp,
				   output logic [1:0] ResultSrc, ALUSrcB);
					
			logic [29:0] cw;			
			logic [4:0] adr ; 
			
			
			
			controlMemory cm( adr , cw );
			branchLogic bl(clk,reset,cw,Op,Funct,adr);
			
			
			// assign outputs here 
			assign {Branch,ALUOp,NextPC,RegW,MemW,IRWrite,AdrSrc,ResultSrc,ALUSrcA,ALUSrcB} =
						{ cw[29:28],cw[24:15] } ;
			
							
endmodule 



module branchLogic( input logic clk,reset,
						  input logic [29:0] cw,
						  input logic [1:0] op,
						  input logic [5:0] funct,
						  output logic [4:0] nextAdr);
						 

			always_ff@(posedge clk,posedge reset)
				if(reset)
					nextAdr <= 5'b11111;
				else 
					begin 
						case( cw[4:0] ) 
							5'b01010:
								nextAdr <= nextAdr+5'b00001;
								
							5'b01011:
								if(op==2'b01)
									nextAdr <= 5'b00010;
								else if(op==2'b10)
									nextAdr <= 5'b01001;
								else
									if(funct[5]== 0)
										nextAdr <= 5'b00110;
									else
										nextAdr <= 5'b00111;
										
										
							5'b01100:
								if( funct[0]==0)
										nextAdr <= 5'b00101;
								else
										nextAdr <= 5'b00011;
										
										
							default:
								nextAdr <= cw[4:0];
							endcase
						end
						 
endmodule




module controlMemory(input logic[4:0] adr,
			  output logic [29:0] dout);
	always_comb
		case(adr)
			// 01010 : Increment 
			// 01011 : Instruction Register
			// 01100 : ConditionCheck
			
			5'b00000: dout = 30'b000001001010110xxxxxx_xxxx_01010;
			
			5'b00001: dout = 30'b000000000x10110xxxxxx_xxxx_01011;
			
			5'b00010: dout = 30'b000000000xxx001xxxxxx_xx0x_01100;
			
			5'b00011: dout = 30'b000000100100xxxxxxxxx_xxxx_01010;
			
			5'b00100: dout = 30'b000000100x01xxxxxxxxx_xxxx_00000;
			
			5'b00101: dout = 30'b000000010100xxxxxxxxx_xxxx_00000;
			
			5'b00110: dout = 30'b010000000xxx000xxxxxx_xxxx_01000;
			
			5'b00111: dout = 30'b010000000xxx001xxxxxx_xxxx_01000;
			
			5'b01000: dout = 30'b000000100x00xxxxxxxxx_xxxx_00000;
			
			5'b01001: dout = 30'b100000000x10001xxxxxx_xxxx_00000;
			
			default: dout= 0;
			
		endcase 
	
endmodule

module condlogic(input  logic       clk, reset, 
                 input  logic [3:0] Cond, 
                 input  logic [3:0] ALUFlags, 
                 input  logic [1:0] FlagW, 
                 input  logic       PCS, NextPC, RegW, MemW, 
                 output logic       PCWrite, RegWrite, MemWrite); 
 
  logic [1:0] FlagWrite; 
  logic [3:0] Flags; 
  logic       CondEx, CondExDelayed; 
 
  flopenr #(2) flagreg1(clk, reset, FlagWrite[1], ALUFlags[3:2],  
Flags[3:2]); 

  flopenr #(2) flagreg0(clk, reset, FlagWrite[0], ALUFlags[1:0],  
Flags[1:0]); 
 
  // write controls are conditional 
  condcheck cc(Cond, Flags, CondEx); 
  flopr #(1)condreg(clk, reset, CondEx, CondExDelayed); 
  assign FlagWrite = FlagW & {2{CondEx}}; 
  assign RegWrite  = RegW  & CondExDelayed; 
  assign MemWrite  = MemW  & CondExDelayed; 
  assign PCWrite   = (PCS  & CondExDelayed) | NextPC; 
  
endmodule     



module condcheck(input  logic [3:0] Cond, 
                 input  logic [3:0] Flags, 
                 output logic       CondEx); 
 
  logic neg, zero, carr, overflow, ge; 
   
  assign {neg, zero, carr, overflow} = Flags; 
  assign ge = (neg == overflow); 
                   
  always_comb 
    case(Cond) 
      4'b0000: CondEx = zero;             // EQ 
      4'b0001: CondEx = ~zero;            // NE 
      4'b0010: CondEx = carr;             // CS 
      4'b0011: CondEx = ~carr;            // CC 
      4'b0100: CondEx = neg;              // MI 
 

      4'b0101: CondEx = ~neg;             // PL 
      4'b0110: CondEx = overflow;         // VS 
      4'b0111: CondEx = ~overflow;        // VC 
      4'b1000: CondEx = carr & ~zero;     // HI 
      4'b1001: CondEx = ~(carr & ~zero);  // LS 
      4'b1010: CondEx = ge;               // GE 
      4'b1011: CondEx = ~ge;              // LT 
      4'b1100: CondEx = ~zero & ge;       // GT 
      4'b1101: CondEx = ~(~zero & ge);    // LE 
      4'b1110: CondEx = 1'b1;             // Always 
      default: CondEx = 1'bx;             // undefined 
    endcase
	 
endmodule 


// Help Modules :
module flopr #(parameter WIDTH = 8) 
              (input  logic             clk, reset, 
               input  logic [WIDTH-1:0] d,  
               output logic [WIDTH-1:0] q); 
 
  always_ff @(posedge clk, posedge reset) 
    if (reset) q <= 0; 
    else       q <= d; 
endmodule 



module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule


module flopenr #(parameter WIDTH = 8) 
                (input  logic             clk, reset, en, 
                 input  logic [WIDTH-1:0] d,  
                 output logic [WIDTH-1:0] q); 
 
  always_ff @(posedge clk, posedge reset) 
    if (reset)   q <= 0;

    else if (en) q <= d; 
endmodule 

module flopr2 #(parameter WIDTH = 8) 
              (input  logic             clk, reset, 
               input  logic [WIDTH-1:0] d,  
               output logic [WIDTH-1:0] q); 
 
  always_ff @(negedge clk, posedge reset) 
    if (reset) q <= 0; 
    else       q <= d; 
endmodule 

module mux2 #(parameter WIDTH = 8) 
             (input  logic [WIDTH-1:0] d0, d1,  
              input  logic             s,  
              output logic [WIDTH-1:0] y); 
 
  assign y = s ? d1 : d0;  
endmodule 


module alu(input  logic [31:0] a, b, 
           input  logic [1:0]  ALUControl, 
           output logic [31:0] Result, 
           output logic [3:0]  ALUFlags); 
 
  logic        neg, zero, carr, overflow; 
  logic [31:0] condinvb; 
  logic [32:0] sum; 
 
  assign condinvb = ALUControl[0] ? ~b : b; 
  assign sum = a + condinvb + ALUControl[0]; 
 
  always_comb 
    casex (ALUControl[1:0]) 
      2'b0?: Result = sum; 
      2'b10: Result = a & b; 
      2'b11: Result = a | b; 
    endcase 
 
  assign neg      = Result[31]; 
  assign zero     = (Result == 32'b0); 
  assign carr    = (ALUControl[1] == 1'b0) & sum[32]; 
 assign overflow = (ALUControl[1] == 1'b0) & ~(a[31] ^ b[31] ^ 
 ALUControl[0]) & (a[31] ^ sum[31]); 
  assign ALUFlags = {neg, zero, carr, overflow}; 
endmodule


