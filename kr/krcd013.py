# Python interface to an interactive theorem prover (e.g., ProofPower) (coded by Gemini 3 Pro)

import subprocess
import time

class ProverInterface:
    def __init__(self, command, prompt_marker=":) "):
        self.prompt_marker = prompt_marker
        self.process = subprocess.Popen(
            command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, # Some provers print banners/prompts to stderr
            text=True,
            bufsize=0  # Unbuffered is crucial for interactive sessions
        )
        # Read the initial banner until the first prompt appears
        self.read_until_prompt()

    def read_until_prompt(self):
        output = []
        while True:
            # Read one character at a time to avoid blocking on a line that never ends
            # (Prompts often don't end with a newline)
            char = self.process.stdout.read(1)
            if not char:
                break # EOF
            output.append(char)
            
            # Check if the buffer ends with our prompt marker
            # Optimization: only check the last N chars where N = len(marker)
            current_tail = "".join(output[-len(self.prompt_marker):])
            if current_tail == self.prompt_marker:
                break
        
        return "".join(output)

    def run_command(self, cmd_str):
        if self.process.poll() is not None:
            raise Exception("Prover process has exited.")
            
        # Write the command (ensure newline)
        self.process.stdin.write(cmd_str + "\n")
        
        # Read the result up to the next prompt
        return self.read_until_prompt()

    def close(self):
        self.process.terminate()

# Example Usage (Hypothetical ProofPower command)
# pp = ProverInterface(["pp", "-d", "spade.polydb"], prompt_marker=":) ")
# print(pp.run_command("val x = 1;")) 
# pp.close()