/*
 *
*/
sig Repository {
	file: FileName -> one File
}

sig Local -- ワーキングディレクトリ 
{
	file: FileName -> one File
//	file: set File
}

sig File {}
sig FileName {}
//sig リビジョン {}

sig ChangeSet {
	file2: FileName -> one File
}

pred commit[r,r': Repository, cs: ChangeSet] {
	r'.file = r.file ++ cs.file2
	some cs.file2 => some (cs.file2 - r.file)
//	some n: FileName | cs.file[n] != r.file[n]
//	(some (r.file - r'.file) or some (r'.file - r.file))
}
pred editandcommit[l,l':Local, r,r'':Repository] {
	some cs: ChangeSet | cs.file2 = l'.file - l.file implies commit[r,r'',cs]
}
pred commit_test[l,l':Local, r,r'':Repository] {
	editandcommit[l, l', r, r'']
	some (l'.file - l.file)
	some (r.file - r''.file)
}
run commit_test
fact {
//	#FileName = 1
//	lone (Repository.file).File
//	some r, r' : Repository | one cs: ChangeSet  | some cs.file2 && commit[r, r', cs]
}

pred update[l,l': Local, r:Repository] { // checkout, update
	r.file in l'.file
	//l'.file = l.file ++ r.file
}
/*
pred update[m: (FileName->File)] {
}
*/
run commit
run commit for 2 but 2 FileName,//* for 2 but exactly 1 FileName, 
exactly 2 Repository//, exactly 1 ChangeSet*/
run update
