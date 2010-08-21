<?php

include("../dataupload/initDB.php");

//connect to DB, those who opened it has to be responsible closing it using the returned dbhandle.
$dbhandle = initializeDB("citytesting+citytesting");

$result = mysql_query("SELECT * FROM raw_data_links order by id desc limit 100");

echo "<h2>Raw Data</h2><br>
<table border='1'>
<tr>
<th>id</th>
<th>subject_id</th>
<th>server_date_time</th>
<th>date_string</th>
<th>unix_time</th>
<th>gmt</th>
<th>hyperlink</th>
<th>notes</th>
</tr>";

while($row = mysql_fetch_array($result))
{
	echo "<tr>";
	echo "<td>" . $row['id'] . "</td>";
	echo "<td>" . $row['subject_id'] . "</td>";
	echo "<td>" . $row['server_date_time'] . "</td>";
	echo "<td>" . $row['date_string'] . "</td>";
	echo "<td>" . $row['unix_time'] . "</td>";
	echo "<td>" . $row['gmt'] . "</td>";
	echo "<td><a href=\"".$row['hyperlink']."\">" . basename($row['hyperlink']) . "</a>
	</td>";
	echo "<td>" . $row['notes'] . "</td>";
	echo "</tr>";
}
echo "</table>";

$result = mysql_query("SELECT * FROM log_links order by id desc limit 100");

echo "<h2>Log Data</h2><br>
<table border='1'>
<tr>
<th>id</th>
<th>subject_id</th>
<th>server_date_time</th>
<th>date_string</th>
<th>unix_time</th>
<th>gmt</th>
<th>hyperlink</th>
<th>notes</th>
</tr>";

while($row = mysql_fetch_array($result))
{
	echo "<tr>";
	echo "<td>" . $row['id'] . "</td>";
	echo "<td>" . $row['subject_id'] . "</td>";
	echo "<td>" . $row['server_date_time'] . "</td>";
	echo "<td>" . $row['date_string'] . "</td>";
	echo "<td>" . $row['unix_time'] . "</td>";
	echo "<td>" . $row['gmt'] . "</td>";
	echo "<td><a href=\"".$row['hyperlink']."\">" . basename($row['hyperlink']) . "</a>
	</td>";
	echo "<td>" . $row['notes'] . "</td>";
	echo "</tr>";
}
echo "</table>";


mysql_close($dbhandle);

?>