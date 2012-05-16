/*
 *
*/
sig Repository {
	file: FileName one -> one File
}
/*
sig Local -- ワーキングディレクトリ 
{
	file: FileName one -> one File
//	file: set File
}
*/
sig File {}
sig FileName {}
//sig リビジョン {}

sig ChangeSet {
	file: FileName  one -> one File
}

pred commit[r,r': Repository, cs: ChangeSet] {
	r'.file = r.file ++ cs.file
	some cs.file => some (cs.file - r.file)
//	some (cs.file - r.file)
	//some n: FileName | cs.file[n] != r.file[n]
//	(some (r.file - r'.file) or some (r'.file - r.file))
}

fact {
//	lone (Repository.file).File
	some r, r' : Repository | one cs: ChangeSet  | some cs.file && commit[r, r', cs]
}

/*

pred update[l,l': Local, r:Repository] { // checkout, update
	l'.file = l.file ++ r.file
}
pred update[m: (FileName->File)] {
}
*/
run commit for 2 but 1 FileName,//* for 2 but exactly 1 FileName, 
exactly 2 Repository//, exactly 1 ChangeSet*/
