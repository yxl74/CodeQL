import java
import codeql.xml.Xml
import semmle.code.xml.AndroidManifest

predicate getPermissionLevel(string permName, string permLevel) {
  exists(AndroidManifestXmlFile manifest, XmlElement permElement |
    permElement.getFile() = manifest and
    permElement.getName() = "permission" and
    permElement.getAttributeValue("android:name") = permName and
    permLevel = permElement.getAttributeValue("android:protectionLevel")
  )
}

predicate isAndroidPermission(string permName) {
  permName.matches("android.permission.%")
}

from AndroidManifestXmlFile manifest, AndroidComponentXmlElement component, string permNeeded, string permLevel
where 
    component.getFile() = manifest and
    component.isExported() and
    exists(XmlAttribute attr |
      attr = component.getAnAttribute() and
      attr.getName().matches("%ermission%") and
      permNeeded = attr.getValue()
    ) and
    (
      if getPermissionLevel(permNeeded, permLevel)
      then permLevel = permLevel
      else
        if isAndroidPermission(permNeeded)
        then permLevel = "system"
        else permLevel = "undefined"
    )
select
    manifest.getAbsolutePath() as filepath,
    component.getName() as type,
    component.getResolvedComponentName() as name,
    permNeeded as permissionNeeded,
    permLevel as permissionLevel
