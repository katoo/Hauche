#!/usr/local/bin/hosh
<html>
<head>
<title>Hauche</title>
</head>
<body onload='document.f.i.focus()'>
<form name=f>
<input name=i size=80 value='<%=cgi i%>'>
<input value=eval type=submit>
</form>
<%=i.cgi.evl.htmlEsc%>
</body>
</html>
