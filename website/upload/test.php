<?php



echo "<pre>";
print_r($_SERVER['DOCUMENT_ROOT']);

printf('\n\n\nDirectory of .\n');
$d = dir('.');
print_r($d);
while (false !== ($entry = $d->read())) {
   echo $entry."\n";
}

printf('Directory of ../\n');
$d = dir('../');
print_r($d);
while (false !== ($entry = $d->read())) {
   echo $entry."\n";
}


printf('Directory of /\n');
$d = dir('/');
print_r($d);
while (false !== ($entry = $d->read())) {
   echo $entry."\n";
}


printf('Directory of data_store\n');
$d = dir('data_store');
print_r($d);
while (false !== ($entry = $d->read())) {
   echo $entry."\n";
}


$directory = '/afs/athena.mit.edu/org/c/citytesting/web_scripts';
printf('Directory of "%s"\n', $directory);
$d = dir($directory);
print_r($d);
while (false !== ($entry = $d->read())) {
   echo $entry."\n";
}



?>