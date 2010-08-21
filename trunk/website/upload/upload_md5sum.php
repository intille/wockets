<?php 
//$requireSSL = true;
// If page requires SSL, and we're not in SSL mode, 
// redirect to the SSL version of the page
//if($requireSSL && $_SERVER['SERVER_PORT'] != 443) {
//   header("HTTP/1.1 301 Moved Permanently");
//   header("Location: https://".$_SERVER['HTTP_HOST'].$_SERVER['REQUEST_URI']);
//   exit("SSL required");
//}

if( isset($_POST['displayExecuteTime'])) {
	$mtime = microtime(); 
	$mtime = explode(" ",$mtime); 
	$mtime = $mtime[1] + $mtime[0]; 
	$starttime = $mtime; 
}

//------------------------------------------------------------
// Get the targetPath from the POSTed UUID:
$uuid = escapeshellcmd($_POST['uuid']);
if( !isset($_POST['uuid']) )
	exit( "No UUID specified");
include_once($_SERVER['DOCUMENT_ROOT']."/initDB.php");
$dbhandle = initDB();
$uuid = mysql_real_escape_string($uuid);
$selectQuery = "SELECT targetPath FROM uploaded_files WHERE uuid = UNHEX('$uuid');";
$result = mysql_query($selectQuery);
$row = mysql_fetch_assoc($result);
$targetPath = $row['targetPath'];
mysql_close($dbhandle);


//------------------------------------------------------------
// Process defaults and override with POST settings:
$chunkSize    = 1024*1024; // 1MB default chunk size
$perChunkSums = true;      // Calculate an array of MD5sum's every chunkSize blocks
$algo         = "md5";

if( isset($_POST['chunkSize']) )
	$chunkSize = (int)$_POST['chunkSize'];

if( isset( $_POST['perChunkSums']) ) {
	if( (int)$_POST['perChunkSums'] >= 1 )
		$perChunkSums = true;
	else
		$perChunkSums = false;
}


// Select hash algorithm from available set
if( isset( $_POST['algo']) ) {
	$hashArray = hash_algos();
	$result    = array_search( escapeshellcmd($_POST['algo']), $hashArray );
	if( $result === false )
		// error, user selected an invalid hash algorithm, use the default
		$algo = $algo;
	else
		$algo = $hashArray[$result];
}



//------------------------------------------------------------
// Check if the file exists, open, determine how many chunk's we'll need:
if( file_exists($targetPath) ) {
	$stats = stat($targetPath);
	$file = fopen($targetPath,'rb');
}
else
	exit;
$numChunks = ceil($stats['size']/$chunkSize);
if( false ) {
	printf("\nNumChunks: ");
	print_r($numChunks);
	printf("\nchunkSizes: ");
	print_r($chunkSize);
	printf("\n");
	print_r($targetPath);
	printf("\n");
	print_r($stats);
	printf("\n");
	print_r($stats['size']);
	printf("\n");
}



//------------------------------------------------------------
// Hash the file:
$md5sum = hash_init($algo);
$chunk_md5_sum  = array();
$chunk_md5_lo   = array();
$chunk_md5_hi   = array();


$chunk_curOut = 0;
$cur_lo = 0;
$cur_hi = 0;
set_time_limit(0);
while( $file && !feof($file) ) {
	$data = fread( $file, $chunkSize );
	hash_update($md5sum,$data);
	
	$cur_lo = $cur_hi;
	$cur_hi = $cur_hi + strlen($data)-1;
	
	// Create a hash for each intermediate chunk
	if( $perChunkSums ) {
		$chunk_md5_cur = hash_init($algo);
		hash_update($chunk_md5_cur,$data);
		$chunk_md5_sum[$chunk_curOut] = hash_final($chunk_md5_cur);
		$chunk_md5_lo[ $chunk_curOut] = $cur_lo;
		$chunk_md5_hi[ $chunk_curOut] = $cur_hi;
		
		$chunk_curOut++;
	}
	if( !feof($file) )
		$cur_hi++;
}
$md5sum_string = hash_final($md5sum);
set_time_limit(30);



//------------------------------------------------------------
// Return the data as text. You can also return it as header meta data (using header):
header("HTTP/1.1 200 OK");
echo '<pre>';
printf("Hash-Algo: %s\n", $algo);
printf("Hash: bytes %d-%d/%d %s\n", 0, $cur_hi, $stats['size'], $md5sum_string);
if( $chunk_md5_sum ) {
	for( $cur=0; $cur<count($chunk_md5_sum); $cur++ ) {
		printf("Hash-Chunk: bytes %d-%d/%d %s\n", $chunk_md5_lo[$cur], $chunk_md5_hi[$cur], $stats['size'], $chunk_md5_sum[$cur]);
	}
}





//------------------------------------------------------------
// Error checking:
if( false ) {
	printf( "split %s -b %d md5.parts.\n\n", $targetPath, $chunkSize );
	$cur = 0;
	foreach( $chunk_md5_sum as $sum ) {
		$n = sprintf( "%02d", $cur );
		$cur++;
		for($r = ""; $n >= 0; $n = intval($n / 26) - 1)
			$r = chr($n%26 + 0x61) . $r;
		if( strlen($r) == 1 )
			$r = "a$r";
		printf( "%s  md5.parts.%s\n", $sum, $r);		
	}
	printf( "Put the md5sums into a file and check with  md5sum -c ./n.txt\n" );
	print_r($chunk_md5_sum);
	print_r($chunk_md5_lo);
	print_r($chunk_md5_hi);
}

if( isset($_POST['displayExecuteTime'])) {
	$mtime = microtime(); 
	$mtime = explode(" ",$mtime); 
	$mtime = $mtime[1] + $mtime[0]; 
	$endtime = $mtime; 
	$totaltime = ($endtime - $starttime); 
	echo "This page was created in ".$totaltime." seconds"; 
}
echo '</pre>';
;?>
