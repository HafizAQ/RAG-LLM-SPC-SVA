**RAG-LLM-SPC-SVA**

**Enhanced VLSI Assertion Generation: Aligning with High-Level Specifications and Minimizing LLM Hallucinations Using RAG**


**Overview**

This repository provides a framework for generating SystemVerilog Assertions (SVAs) for VLSI design verification using a Retrieval-Augmented Generation (RAG) approach in conjunction with Large Language Models (LLMs). 
The method aims to ensure conformity to high-level specifications (HLS) and reduce the potential for hallucinations inherent in LLM-generated assertions.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**Steps**

**1) Data Preparation***

  i) Case Study - High-Level Specification (HLS) Document:

    Source document: AMBA AX4 Lite Protocol PDF (AMBA AXI Protocol Specification: https://developer.arm.com/documentation/ihi0022/).
    
    Convert the PDF document into Markdown format for structured referencing.

  ii) Designer Specifications:
  
    Define designer-side specifications for intended SystemVerilog Assertions (SVAs) generation.

  iii) Golden DUV (Design-Under-Verification):
    Use a verified golden DUV for comparison and validation of generated assertions.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**2) Experimental Steps**

  i) Setup and API Key:

    Provide the OpenAI API key for chat completion.

  ii) File References:

    Ensure references to the HLS document, designer specifications, and golden DUV are accessible within the setup.

  iii) Prompt Engineering:

    Utilize prompts from the prompt-engineering file to assign specific roles to the LLM for efficient and contextually accurate assertion generation.

  iv) Execution: 

    Run the code (Enhanced_VLSI_Assertion_Generation_Conforming_to_High_Level_Specifications_and_Reducing_LLM_Hallucinations_with_RAG.ipynb) to generate assertions and knowledge-based results from the LLM.
    
    Store the generated assertions and results for subsequent validation.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**3) Evaluation Using Bounded Model Checking (BMC)**

  i) Validation Setup:

    To verify generated assertions against the DUV, employ formal property verification through Bounded Model Checking (BMC).

  ii) Tool Setup:

    Download and install the Tabby-CAD toolset for BMC (https://www.yosyshq.com/tabby-cad-datasheet).

  iii) Assertion Integration:

    Insert the RAG-LLM-generated assertions into the golden DUV code.

  iv) Execution and Verification:

    Run Tabby-CAD to execute and validate the assertions, comparing outcomes against the original DUV specifications.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**Applicability**

  The RAG-LLM approach can be extended to other case studies and is compatible with future versions of foundation/ language models, such as GPTs, Llama, and beyond.
