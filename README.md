sudo apt update
sudo apt install -y curl git build-essential
sudo apt install -y clang

curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
(when prompted just choose the default stable option)
source ~/.profile
Verify with:
lean --version
lake --version

Install VsCode, then go to extensions and search for Lean 4. leanprover.lean4 should be the extension, and then restart.

Create a new project with mathlib:
mkdir -p ~/lean-projects
cd ~/lean-projects
lake new MyProject math
cd MyProject
lake exe cache get
lake build

And then open in vscode
code .

Make a test file:
touch MyProject/Test.lean
